// reln.c ... functions on Relations
// part of Multi-attribute Linear-hashed Files
// Last modified by John Shepherd, July 2019

#include "defs.h"
#include "reln.h"
#include "page.h"
#include "tuple.h"
#include "chvec.h"
#include "bits.h"
#include "hash.h"

#define HEADERSIZE (3*sizeof(Count)+sizeof(Offset))

struct RelnRep {
	Count  nattrs; // number of attributes
	Count  depth;  // depth of main data file
	Offset sp;     // split pointer
    Count  npages; // number of main data pages
    Count  ntups;  // total number of tuples
	ChVec  cv;     // choice vector
	char   mode;   // open for read/write
	FILE  *info;   // handle on info file
	FILE  *data;   // handle on data file
	FILE  *ovflow; // handle on ovflow file
	int insertions; // keeps track of how many insertions since last split
};

// create a new relation (three files)

Status newRelation(char *name, Count nattrs, Count npages, Count d, char *cv)
{
    char fname[MAXFILENAME];
	Reln r = malloc(sizeof(struct RelnRep));
	r->nattrs = nattrs; r->depth = d; r->sp = 0;
	r->npages = npages; r->ntups = 0; r->mode = 'w'; r->insertions = 0;
	assert(r != NULL);
	if (parseChVec(r, cv, r->cv) != OK) return ~OK;
	sprintf(fname,"%s.info",name);
	r->info = fopen(fname,"w");
	assert(r->info != NULL);
	sprintf(fname,"%s.data",name);
	r->data = fopen(fname,"w");
	assert(r->data != NULL);
	sprintf(fname,"%s.ovflow",name);
	r->ovflow = fopen(fname,"w");
	assert(r->ovflow != NULL);
	int i;
	for (i = 0; i < npages; i++) addPage(r->data);
	closeRelation(r);
	return 0;
}

// check whether a relation already exists

Bool existsRelation(char *name)
{
	char fname[MAXFILENAME];
	sprintf(fname,"%s.info",name);
	FILE *f = fopen(fname,"r");
	if (f == NULL)
		return FALSE;
	else {
		fclose(f);
		return TRUE;
	}
}

// set up a relation descriptor from relation name
// open files, reads information from rel.info

Reln openRelation(char *name, char *mode)
{
	Reln r;
	r = malloc(sizeof(struct RelnRep));
	assert(r != NULL);
	char fname[MAXFILENAME];
	sprintf(fname,"%s.info",name);
	r->info = fopen(fname,mode);
	assert(r->info != NULL);
	sprintf(fname,"%s.data",name);
	r->data = fopen(fname,mode);
	assert(r->data != NULL);
	sprintf(fname,"%s.ovflow",name);
	r->ovflow = fopen(fname,mode);
	assert(r->ovflow != NULL);
	// Naughty: assumes Count and Offset are the same size
	int n = fread(r, sizeof(Count), 5, r->info);
	assert(n == 5);
	n = fread(r->cv, sizeof(ChVecItem), MAXCHVEC, r->info);
	assert(n == MAXCHVEC);
	r->mode = (mode[0] == 'w' || mode[1] =='+') ? 'w' : 'r';
	return r;
}

// release files and descriptor for an open relation
// copy latest information to .info file

void closeRelation(Reln r)
{
	// make sure updated global data is put in info
	// Naughty: assumes Count and Offset are the same size
	if (r->mode == 'w') {
		fseek(r->info, 0, SEEK_SET);
		// write out core relation info (#attr,#pages,d,sp)
		int n = fwrite(r, sizeof(Count), 5, r->info);
		assert(n == 5);
		// write out choice vector
		n = fwrite(r->cv, sizeof(ChVecItem), MAXCHVEC, r->info);
		assert(n == MAXCHVEC);
	}
	fclose(r->info);
	fclose(r->data);
	fclose(r->ovflow);
	free(r);
}

// insert a new tuple into a relation
// returns index of bucket where inserted
// - index always refers to a primary data page
// - the actual insertion page may be either a data page or an overflow page
// returns NO_PAGE if insert fails completely
// TODO: include splitting and file expansion

PageID addToRelation(Reln r, Tuple t)
{
	// Check if we need to split
	int threshold = (PAGESIZE / (10 * r->nattrs) > 1 ) ? PAGESIZE / (10 * r->nattrs) : 1; // Make sure we don't split every 0 insertions  
	if (r->insertions >= threshold) {
		// Need to split
		split(r);
		r->sp ++;
		if (r->sp == power_helper(2, r->depth)) { r->depth ++; r->sp = 0; }
		r->insertions = 0;
	}


	Bits h, p;
	// char buf[MAXBITS+1];
	h = tupleHash(r,t);
	if (r->depth == 0)
		p = 0; // bug fix
	else {
		p = getLower(h, r->depth);
		if (p < r->sp) p = getLower(h, r->depth+1);
	}
	// bitsString(h,buf); printf("hash = %s\n",buf);
	// bitsString(p,buf); printf("page = %s\n",buf);
	Page pg = getPage(r->data,p);
	if (addToPage(pg,t) == OK) {
		printf("Tuple '%s' added to page %u\n", t, p);
		putPage(r->data,p,pg);
		r->insertions ++;
		r->ntups ++;
		return p;
	}
	// primary data page full
	if (pageOvflow(pg) == NO_PAGE) {
		// add first overflow page in chain
		PageID newp = addPage(r->ovflow);
		pageSetOvflow(pg,newp);
		putPage(r->data,p,pg);
		Page newpg = getPage(r->ovflow,newp);
		// can't add to a new page; we have a problem
		if (addToPage(newpg,t) != OK) return NO_PAGE;
		putPage(r->ovflow,newp,newpg);
		r->insertions ++;
		r->ntups ++;
		return p;
	}
	else {
		// scan overflow chain until we find space
		// worst case: add new ovflow page at end of chain
		Page ovpg, prevpg = NULL;
		PageID ovp, prevp = NO_PAGE;
		ovp = pageOvflow(pg);
		while (ovp != NO_PAGE) {
			ovpg = getPage(r->ovflow, ovp);
			if (addToPage(ovpg,t) != OK) {
				prevp = ovp; prevpg = ovpg;
				ovp = pageOvflow(ovpg);
			}
			else {
				if (prevpg != NULL) free(prevpg);
				putPage(r->ovflow,ovp,ovpg);
				r->ntups ++;
				r->insertions ++;
				return p;
			}
		}
		// all overflow pages are full; add another to chain
		// at this point, there *must* be a prevpg
		assert(prevpg != NULL);
		// make new ovflow page
		PageID newp = addPage(r->ovflow);
		// insert tuple into new page
		Page newpg = getPage(r->ovflow,newp);
        if (addToPage(newpg,t) != OK) return NO_PAGE;
        putPage(r->ovflow,newp,newpg);
		// link to existing overflow chain
		pageSetOvflow(prevpg,newp);
		putPage(r->ovflow,prevp,prevpg);
        r->ntups ++;
		r->insertions ++;
		return p;
	}
	return NO_PAGE;
}

// external interfaces for Reln data

FILE *dataFile(Reln r) { return r->data; }
FILE *ovflowFile(Reln r) { return r->ovflow; }
Count nattrs(Reln r) { return r->nattrs; }
Count npages(Reln r) { return r->npages; }
Count ntuples(Reln r) { return r->ntups; }
Count depth(Reln r)  { return r->depth; }
Count splitp(Reln r) { return r->sp; }
ChVecItem *chvec(Reln r)  { return r->cv; }


// displays info about open Reln

void relationStats(Reln r)
{
	printf("Global Info:\n");
	printf("#attrs:%d  #pages:%d  #tuples:%d  d:%d  sp:%d\n",
	       r->nattrs, r->npages, r->ntups, r->depth, r->sp);
	printf("Choice vector\n");
	printChVec(r->cv);
	printf("Bucket Info:\n");
	printf("%-4s %s\n","#","Info on pages in bucket");
	printf("%-4s %s\n","","(pageID,#tuples,freebytes,ovflow)");
	for (Offset pid = 0; pid < r->npages; pid++) {
		printf("[%2d]  ",pid);
		Page p = getPage(r->data, pid);
		Count ntups = pageNTuples(p);
		Count space = pageFreeSpace(p);
		Offset ovid = pageOvflow(p);
		printf("(d%d,%d,%d,%d)",pid,ntups,space,ovid);
		free(p);
		while (ovid != NO_PAGE) {
			Offset curid = ovid;
			p = getPage(r->ovflow, ovid);
			ntups = pageNTuples(p);
			space = pageFreeSpace(p);
			ovid = pageOvflow(p);
			printf(" -> (ov%d,%d,%d,%d)",curid,ntups,space,ovid);
			free(p);
		}
		putchar('\n');
	}
}

int power_helper(int base, int power) {
	if (power == 0) {
		return 1;
	} else {
		return base * power_helper(base, power - 1);
	}
}


void split(Reln r) {
	Count d = r->depth;
	Offset sp = r->sp;

	PageID oldp = sp;
	PageID newp = sp + power_helper(2, d);
	Offset currtup = 0;
	PageID currpageid = oldp;
	int is_old_ovflow = FALSE;
	int is_new_ovflow = FALSE;

	Page pg = getPage(r->data, currpageid);
	PageID newpageid = addPage(r->data);
	r->npages ++;
	assert(newpageid = newp);
	Page newpg = getPage(r->data, newpageid);



	while (currpageid != NO_PAGE) {
		if (is_old_ovflow) pg = getPage(r->ovflow, currpageid);


		currtup = 0;
		while (currtup < pageFree(pg)) {
			Tuple t = pageData(pg) + currtup;
			Bits hash = getLower(tupleHash(r, t), d + 1);
			if (hash == oldp) {
				currtup += strlen(t) + 1;
			} else {
				// Decide where in the new page/overflow we are adding the tuple
				if (addToPage(newpg, t) != OK) {

					PageID prevpageid = newpageid;
					newpageid = addPage(r->ovflow);
					newpg = getPage(r->ovflow, newpageid);


					Page prevpage = (is_new_ovflow) ? getPage(r->ovflow, prevpageid) : getPage(r->data, prevpageid);
					pageSetOvflow(prevpage, newpageid);

					if (is_new_ovflow) {
						putPage(r->ovflow, prevpageid, prevpage);
					} else {
						putPage(r->data, prevpageid, prevpage);
					}
					
					is_new_ovflow = TRUE;

					// can't add to a new page; we have a problem
					if (addToPage(newpg, t) != OK) {
						printf("Tuple too big to insert?");
						return;
					}
					// putPage(r->ovflow, newpageid, newpg); // Writes the new page with tuple to the overflow file

				} else if (is_new_ovflow == FALSE) {
					// putPage(r->data, newpageid, newpg);
				} else {
					// putPage(r->ovflow, newpageid, newpg);
				}

				// Clean up the old page
				int bytes_to_copy = pageFree(pg) - (currtup + strlen(t) + 1);
				int decrease = strlen(t) + 1;
				
				char *temp = malloc(bytes_to_copy);
				memcpy(temp, pageData(pg) + currtup + decrease, bytes_to_copy);
				memcpy(pageData(pg) + currtup, temp, bytes_to_copy);
				free(temp);
				decreasePageFree(pg, decrease);
				decrementPageTuples(pg);

				if (is_old_ovflow == FALSE) {
					putPage(r->data, currpageid, pg);
					pg = getPage(r->data, currpageid);
				} else {
					putPage(r->ovflow, currpageid, pg);
					pg = getPage(r->ovflow, currpageid);
				}
			}
		} 
		currpageid = pageOvflow(pg);
		free(pg);
		is_old_ovflow = TRUE;
	}


	if (is_new_ovflow == FALSE) {
		putPage(r->data, newpageid, newpg);
	} else {
		putPage(r->ovflow, newpageid, newpg);
	}

	// Logic to split the old page between itself and the new page
	// For each tuple in the oldp data and overflow pages:
	// If it should still be in oldp based on d+1 hash then keep it there (don't touch)
	// But do increment the counter for the offset you're at by strlen
	// Otherwise, copy it over to the new page and put it wherever it's supposed to go in the chain
	// As for how to deal with the old page: bring the rest of the page backwards back to the old offset
	// Will have to do this memcpy or something (not strcpy because we want to do the whole rest of array in one hit)
	// And update the 'free' offset
	// DO NOT have to bring tuples from overflow pages back to the main data page or preceeding overflow pages
	// Just use the offset to indicate 
}