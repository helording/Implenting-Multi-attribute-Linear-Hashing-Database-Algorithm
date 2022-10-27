// query.c ... query scan functions
// part of Multi-attribute Linear-hashed Files
// Manage creating and using Query objects
// Last modified by John Shepherd, July 2019
#include <string.h>
#include <stdio.h>
#include "defs.h"
#include "query.h"
#include "reln.h"
#include "tuple.h"
#include "hash.h"
#include "bits.h"
// #include <math.h>

// A suggestion ... you can change however you like
void getNextBucket(Query q);

int Pow(int X, int Y);

struct QueryRep {
	Reln    rel;       // need to remember Relation info
	Bits    known;     // the hash value from MAH
	Bits    unknown;   // the unknown bits from MAH
	PageID  curpage;   // current page in scan
	int     is_ovflow; // are we in the overflow pages?
	Offset  curtup;    // offset of current tuple within page
	int 	nstars;	   // Number of stars in unkown
	Bits	buck_ind;  // Bucket index
	Tuple 	attris;
};


// take a query string (e.g. "1234,?,abc,?")
// set up a QueryRep object for the scan

Query startQuery(Reln r, char *q)
{
	Query new = malloc(sizeof(struct QueryRep));
	assert(new != NULL);

	int pos = 0;
	int attri = 0;
	int nstars = 0;
	Bits compHash = 0;
	Bits starPos = 0;
	Bits attriHash;
	ChVecItem *vec = chvec(r);

	char *cpy = (char *) calloc(strlen(q) + 1, sizeof(char));
    strcpy(cpy, q);
        
    char *ptr = strtok(cpy, ",");

    while(ptr != NULL)
    {
        if (strcmp(ptr, "?") == 0) {
			// Find unknown bits in hash, set them to 1 in starPos
			for (pos = 0; pos < MAXBITS; pos++){
				if (vec[pos].att == attri) {
					starPos = setBit(starPos, pos);
					nstars++;

				}
			}
		} else {
			// Get hash for attri
			// For associated bits in the chvec for
			// that attribute set in compHash
			attriHash = hash_any((unsigned char *)ptr,strlen(ptr));
			for (pos = 0; pos < MAXBITS; pos++){
				if (vec[pos].att == attri) {
					if (bitIsSet(attriHash, vec[pos].bit)){
							compHash = setBit(compHash, pos);
					}			
				}
			}
		}
        
        ptr = strtok(NULL, ",");
		attri++;
    }
    
    free(cpy);

	Bits p, stp;
	Count d = depth(r);
	Count sp = splitp(r);
	if (d == 0) {
		p = 0;
	} else {
		p = getLower(compHash, d);
		stp = getLower(starPos, d+1);
		
		if (p < sp) {
			p = getLower(compHash, d+1);
		}
		
	}

	nstars = 0;
	for (pos = 0; pos < MAXBITS; pos++) {
		if (bitIsSet(stp, pos) == 1){
			nstars++;
		}
	}

	new->rel = r;
	new->known = p;
	new->unknown = stp;
	new->curpage = p;
	new->is_ovflow = 0;
	new->curtup = 0;
	new->nstars = nstars;
	new->buck_ind = 0;
	new->attris = (Tuple) calloc(strlen(q) + 1, sizeof(char));
	strcpy(new->attris, q);

	return new;
}


Tuple getNextTuple(Query q)
{

	// variables
	Tuple tup;
	Page pg;
	Count hdr_size = 2*sizeof(Offset) + sizeof(Count);

	// get current page
	if (q->is_ovflow) {
		pg = getPage(ovflowFile(q->rel), q->curpage);
	} else {
		pg = getPage(dataFile(q->rel),q->curpage);
	}
	
	// while we dont find a tuple... 
	while (1) {
		if (q->curtup < PAGESIZE-hdr_size-2) {

			// get current tuple pos and update curtup pos
			char *c = pageData(pg) + q->curtup;
			q->curtup += strlen(c) + 1;

			// if tuple empty, skip
			if (strlen(c) == 0){
				continue;
			}

			// if tuple matches, grab tuple and return it
			if (tupleMatch(q->rel,c, q->attris)){
				tup = calloc(strlen(c)+1, sizeof(char));
				memcpy(tup, c, strlen(c));

				return tup;
			}
			
		// if we are at the end of the current page, check
		// if it has a overflow page. Change pages.
		} else if (pageOvflow(pg) != NO_PAGE ) { 

			// grab new page and put in our pg var
			PageID ovp = pageOvflow(pg);
			pg = getPage(ovflowFile(q->rel), ovp);
			
			// new page so simple grab data file for first tuple
			char *c = pageData(pg);

			// Change query variables for new page
			q->curpage = ovp;
			q->curtup = strlen(c) + 1;
			q->is_ovflow = 1;
			
			// if empty skip
			if (strlen(c) == 0){
				continue;
			}

			// if tuple matches, grab tuple and return it
			if (tupleMatch(q->rel, c, q->attris)){
				tup = calloc(strlen(c)+1, sizeof(char));
				memcpy(tup, c, strlen(c));

				return tup;	
			}

		// if we are at the end of the page and theres
		// no more overflow, we must change buckets
		} else {

			// check if current bucket is last to check
			if (q->buck_ind == Pow(2,q->nstars) - 1) {
				return NULL;
			} else {

				getNextBucket(q);

				// check if we've gone past last page 
				if (q->curpage > (Pow(2,depth(q->rel))-1) + splitp(q->rel)){
					return NULL;
				}

				pg = getPage(dataFile(q->rel),q->curpage);

				char *c = pageData(pg);
				q->curtup = strlen(c) + 1;

				if (strlen(c) == 0){
					continue;
				}

				if (tupleMatch(q->rel, c, q->attris)){
					tup = calloc(strlen(c)+1, sizeof(char));
					memcpy(tup, c, strlen(c));

					return tup;	
				}

			}
		}
	}

	return NULL;
}


void getNextBucket(Query q){
	q->buck_ind++;

	Bits mask = 0;
	int changes = 0;
	int i = 0;
	for (i = 0; i < MAXBITS; i++){
		if (bitIsSet(q->unknown, i)) {
			if (bitIsSet(q->buck_ind, changes)){
				mask = setBit(mask, i);
			}
			if (changes++ == q->nstars) break;
		}
	}

	q->curpage = (q->known | mask);
	q->is_ovflow = 0;
	q->curtup = 0;
	
}


// clean up a QueryRep object and associated data

void closeQuery(Query q)
{
	// TODO
}
