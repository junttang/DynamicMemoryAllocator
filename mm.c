/**************************************************
 * Title: SP-Project 3  -  Dynamic Memory Allocator
 * Summary: 'Segregated-Free-List-based Dynamic Me-
 -mory Allocator' for studying the concepts of dyn-
 -amic allocation, various skills to improve space
 utilization, managing the tradeoff between Speedu-
 -p and Peak Memory Utilization.
 *  |Date              |Author             |Version
	|2022-06-28        |Park Junhyeok      |1.0.0
**************************************************/

/****************** Declaration ******************/
/* Headers */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"


/* Preprocessor Directives */
#define WORD			4				/* word, doubleword, chunk(4KB) size */
#define DWORD			8					// to avoid unnecessary indirection,
#define CHUNK			4096				// just using constants directly! 
#define CLASSES			13				/* number of seglist headers */


#define ALIGN(size)		(((size) + (DWORD-1)) & ~0x7)	/* doubleword alignment */
#define VALUE(addr)		(*(size_t *)(addr))				/* extract value from address */
#define HEADER(block)	((char *)(block) - WORD)		/* header of the block */
#define SIZE(block)		(VALUE(HEADER(block)) & ~0x7)	/* size of the block (not just payload) */
#define FLAG(block)		(VALUE(HEADER(block)) & 0x1)	/* is the block allocated? */
#define FOOTER(block)	((char *)(block) + SIZE(block) - DWORD)	/* footer of the block */


#define NEXTB(block)	((char *)(block) + SIZE(block))	/* next or prev block in heap */
#define PREVB(block)	((char *)(block) - (VALUE(((char *)(block) - DWORD)) & ~0x7))


#define NEXTP(block)	(void *)VALUE(block)			/* next or prev block in seglist */
#define PREVP(block)	(void *)VALUE((char *)(block) + WORD)
#define NEXTP_(block)	VALUE(block)						// difference between NEXTP and
#define PREVP_(block)	VALUE((char *)(block) + WORD)		// NEXTP_ is only a purpose!
															// NEXTP_ for avoiding warnings

#define SBRK_ERR		(void *)-1
#define CHECK_PARAM		0				/* operation code for My Consistency Checker */


/* Developer Information */
team_t team = {
	"20171643",							// student ID
	"Junhyeok Park",					// name
	"junttang123@naver.com",			// email
};


/* Global Scalar Variables */
static char *heap_head;					// head of heap
static char **seglist;					// seglist classes


/* Interfaces */
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *, size_t);


/* Subroutines for interfaces */
static void *mm_sbrk(size_t);			// extending heapsize (calling mem_sbrk)
static int mm_check(void);				// my consistency checker (explain later)
static void mm_error(int);				// error reporting function
static int what_class(size_t size);		// return the corresponding class of input size
static void seglist_push(void *target);	// insert into the specific class of seglists
static void seglist_pop(void *target);	// delete from the specific class of seglists
static void *best_fit_search(size_t);	// literally the 'Best Fit Search'
static void *coalesce(int, size_t, void *, // coalescing function
	size_t, void *, size_t, void *);



/**************** Implementation *****************/
/****                Interfaces               ****/
/* setting the initial states of the heap segment */
int mm_init(void) {
	int i;

	if ((seglist = mem_sbrk((CLASSES + 1) * WORD)) == SBRK_ERR) return -1;
	for (i = 0; i < CLASSES; i++)		// seglists are resident in the heap segment
		seglist[i] = NULL;				// initialize each header as NULL

	if ((heap_head = mem_sbrk(4 * WORD)) == SBRK_ERR) return -1;  // allocate intial area

	VALUE(heap_head) = 0x0;							// 1 word padding for alignment
	VALUE(heap_head + 1 * WORD) = (DWORD | 0x1);	// virtual block for handling 
	VALUE(heap_head + 2 * WORD) = (DWORD | 0x1);		// edge cases of each operation 
	VALUE(heap_head + 3 * WORD) = 0x1;				// end of the (virtual) heap segment
	heap_head += DWORD;								// adjust pointing and alignment

	return 0;
}

/* main allocating function, just like 'malloc' of libc! */
void *mm_malloc(size_t size) {
	size_t alloc_size, selected_size, surplus;
	void *ptr, *surplus_p;
	int sbrk_flag = 0;

	if (size == 0) return NULL;
	alloc_size = ALIGN(size + DWORD);				// align!

	if ((ptr = best_fit_search(alloc_size)) == NULL) {	// find proper free block!
		if ((ptr = mm_sbrk(alloc_size)) == NULL)		// if nothing found, then extend
			mm_error(1);
		sbrk_flag = 1;
	}

	selected_size = SIZE(ptr);							// size of selected block
	surplus = selected_size - alloc_size;				// surplus area of selected block

	if (sbrk_flag == 0)							// if 'selected block' is not newly allocated,
		seglist_pop(ptr);						// then, it's freed block that is in seglists!

	/* split routine */
	if (surplus >= 4*WORD) {					// 4 words (header, 2 pointers, footer)
		if (alloc_size >= 20*WORD) {			// to avoid 'Biased Situation' caused by
			surplus_p = ptr;						// alternative allocation (binary-bal.rep),
			ptr = (char *)(ptr) + surplus;			// set a threshold and if surplus pass the
		}											// threshold, then make the left side of
		else surplus_p = (char *)(ptr) + alloc_size; // selected block as surplus (will be freed)

		VALUE(HEADER(ptr)) = (alloc_size | 0x1);
		VALUE(FOOTER(ptr)) = (alloc_size | 0x1);	// ptr points area that will be allocated
		
		VALUE(HEADER(surplus_p)) = surplus;			// surplus_p points surplus area
		VALUE(FOOTER(surplus_p)) = surplus;

		mm_free(surplus_p);							// call mm_free to coalesce! 
	}
	else {
		VALUE(HEADER(ptr)) = (selected_size | 0x1);
		VALUE(FOOTER(ptr)) = (selected_size | 0x1);
	}
	
	return ptr;
}

/* main freeing function, just like 'free' of libc! */
void mm_free(void *ptr) {
	size_t size, prev_size, next_size;
	void *prev_block, *next_block;
	int prev_alloc, next_alloc, option;

	if (ptr == NULL) return;

	size = SIZE(ptr);
	VALUE(HEADER(ptr)) = size;
	VALUE(FOOTER(ptr)) = size;

	prev_block = PREVB(ptr);				// with previous and next block,
	prev_alloc = FLAG(prev_block);				// determine whether to coalesce or not
	prev_size = SIZE(prev_block);

	next_block = NEXTB(ptr);
	next_alloc = FLAG(next_block);
	next_size = SIZE(next_block);

	if (next_alloc == 1 && prev_alloc == 1) option = 1;		// NOT coalesce
	if (next_alloc == 0 && prev_alloc == 1) option = 2;		// coalesce with next block
	if (next_alloc == 1 && prev_alloc == 0) option = 3;		// coalesce with prev block
	if (next_alloc == 0 && prev_alloc == 0) option = 4;		// coalesce with both blocks

	ptr = coalesce(option, size, ptr, next_size, next_block, prev_size, prev_block);
	seglist_push(ptr);						// insert (possibly) coalesced block into seglist
}

/* re-allocating function, just like 'realloc' of libc! */
void *mm_realloc(void *ptr, size_t size) {
	size_t cur_size, want_size, next_size, prev_size, new_size, temp1, temp2;
	void *next_block, *prev_block, *new_block, *NorP_block;
	int next_alloc, prev_alloc, NorP_alloc;

	if (ptr == NULL) return mm_malloc(size);			// handling exceptions 
	if (size == 0) { mm_free(ptr); return NULL; }

	cur_size = SIZE(ptr);							// size of input block
	want_size = ALIGN(size + DWORD);			// size that caller wants
	if (want_size <= cur_size) return ptr;			// if want is smaller, then just return

	/* select the bigger one between previous block and next block */
	next_block = NEXTB(ptr); /**********/ prev_block = PREVB(ptr);
	next_alloc = FLAG(next_block); /****/ prev_alloc = FLAG(prev_block);
	next_size = SIZE(next_block); /*****/ prev_size = SIZE(prev_block);
	temp1 = next_size + cur_size; /*****/ temp2 = prev_size + cur_size;

	new_size = (temp1 > temp2) ? temp1 : temp2;
	new_block = (temp1 > temp2) ? ptr : prev_block;				// selection
	NorP_block = (temp1 > temp2) ? next_block : prev_block;
	NorP_alloc = (temp1 > temp2) ? next_alloc : prev_alloc;

	if (size < cur_size) cur_size = size;						// adjust cur_size

	if (NorP_alloc == 0 && (new_size - want_size) >= DWORD) {	// if (prev/next+curr) can cover
		seglist_pop(NorP_block);								// the want_size, then coalesce,

		memmove(new_block, ptr, cur_size);

		VALUE(HEADER(new_block)) = (new_size | 0x1);			// adjust the block,
		VALUE(FOOTER(new_block)) = (new_size | 0x1);			// and DO NOT split !!!

		return new_block;										// return the coalesced block
	}

	/* if 'selected block with prev/next' cannot cover 'want', then just new alloc!  */
	if ((new_block = mm_malloc(size)) == NULL) mm_error(1);
	memcpy(new_block, ptr, cur_size);
	mm_free(ptr);

	return new_block;
}
/****            End of Interfaces            ****/


/****        Subroutines for interfaces       ****/
/* procedure that coalesce input block with prev or next block (in heap) */
static void *coalesce(
	int option,								// what case?
	size_t size, void *p,					// current block
	size_t nsize, void *np,					// next block of curr
	size_t psize, void *pp					// prev block of curr
) {
	size_t new_size;
	void *front_ptr, *rear_ptr;

	if (option == 1) return p;				// case1
	switch (option) {
	case 2:	new_size = size + nsize;		// case2
		front_ptr = p; rear_ptr = np;
		seglist_pop(np);
		break;
	case 3: new_size = psize + size;		// case3
		front_ptr = pp; rear_ptr = p;
		seglist_pop(pp);
		break;
	case 4: new_size = psize + size + nsize;// case4
		front_ptr = pp; rear_ptr = np;
		seglist_pop(np);
		seglist_pop(pp);
		break;
	default: break;
	}

	VALUE(HEADER(front_ptr)) = (new_size & ~0x7);	// set boundary tags
	VALUE(FOOTER(rear_ptr)) = (new_size & ~0x7);		// as 'freed' with size info

	return front_ptr;
}

/* procedure that find the proper block using 'Best Fit Approach' */
static void *best_fit_search(size_t alloc_size) {
	size_t cur_size, fit_size = (size_t)-1;
	void *iter, *selected = NULL;
	int i, start;

	start = what_class(alloc_size);			// for the size that caller wants,
	for (i = start; i < CLASSES; i++) {		// find the corresponding class by size
		iter = seglist[i];

		while (iter) {						// traverse the selected class (seglist)
			cur_size = SIZE(iter);

			if (FLAG(iter) == 0)
				if (cur_size >= alloc_size && cur_size < fit_size) {
					fit_size = cur_size;
					selected = iter;
				}	// find the minimum block that can cover the 'want_size'

			iter = NEXTP(iter);				// move to next block (in free list, not heap)
		}
	}

	return selected;
}

/* insert newly freed block into the corresponding seglist */
static void seglist_push(void *target) {
	size_t target_size = SIZE(target);
	void *former;

	former = seglist[what_class(target_size)];

	NEXTP_(target) = (size_t)former;			// simply insert into the header of list
	PREVP_(target) = (size_t)NULL;

	if (former != NULL) PREVP_(former) = (size_t)target;

	seglist[what_class(target_size)] = target;
}

/* delete the target free block from the corresponding seglist */
static void seglist_pop(void *target) {
	size_t target_size = SIZE(target);
	void *next, *prev;

	next = NEXTP(target);			// simple 'doubly linked list' node deletion
	prev = PREVP(target);

	if (prev != NULL) NEXTP_(prev) = (size_t)next;	// casting for avoiding warnings
	else seglist[what_class(target_size)] = next;

	if (next != NULL) PREVP_(next) = (size_t)prev;
}

/* return the index of appropriate class, based on 'size' */
static int what_class(size_t size) {
	if (size > 131072) return 12;
	if (size > 32768) return 11;
	if (size > 16384) return 10;
	if (size > 8192) return 9;
	if (size > 4096) return 8;				// 2^k 
	if (size > 2048) return 7;
	if (size > 1024) return 6;
	if (size > 512) return 5;
	if (size > 256) return 4;
	if (size > 128) return 3;
	if (size > 64) return 2;
	if (size > 32) return 1;
	return 0;								// total 13 classes
}

/* extending the size of heap by calling mem_sbrk, with little additioal process */
static void *mm_sbrk(size_t alloc_size) {
	size_t temp, new_size;
	void *ptr;

	temp = ((alloc_size > CHUNK) ?					// default size is CHUNK (4K)
		alloc_size : CHUNK) / WORD;			// choose bigger one (CHUNK vs input size)
	new_size = (temp % 2 == 0) ? (temp*WORD) : ((temp + 1)*WORD);	// align!

	if ((ptr = mem_sbrk(new_size)) == SBRK_ERR) return NULL;

	VALUE(HEADER(ptr)) = new_size;
	VALUE(FOOTER(ptr)) = new_size;
	VALUE((char *)(FOOTER(ptr)) + WORD) = 0x1;	 // end of the (virtual) heap segment

	return ptr;
}

/* error reporting function for 'mm_check' */
static void mm_error(int option) {
	switch (option) {
	case 1: printf("Error occurs during 'sbrk' rouitne.\n"); break;
	case 2: printf("mm_check exits: There're not-free-marked blocks in the free list.\n"); break;
	case 3: printf("mm_check exits: There're contiguous free blocks in the heap.\n"); break;
	case 4: printf("mm_check exits: There're free blocks not in the free list.\n"); break;
	case 5: printf("mm_check exits: There're pointers indicating invalid blocks in the free list.\n"); break;
	case 6: printf("mm_check exits: Some allocated blocks overlap each other.\n"); break;
	case 7: printf("mm_check exits: There're pointers indicating invalid blocks in the heap.\n"); break;
	case 8: printf("mm_check exits: There're blocks that is not aligned by DWORD.\n"); break;
	default: mm_check(); break; // this 'mm_check' call is just for avoiding warnings
	}
	exit(1);
}

/* customized heap consistency checker, you can select the test type via CHECK_PARAM */
static int mm_check(void) {	
	size_t size, byte_cnt, total_size = 0;		// variables used to perform tests below
	int i, prev_f_flag, first_flag = 1, index, found;
	void *iter, *jter, *next;

	switch (CHECK_PARAM) {	// programmer select the type of test by changing CHECK_PARAM
	case 1: /* Test1: Is every block in the free list marked as free? */
		for (i = 0; i < CLASSES; i++)
			if (seglist[i] != NULL) {		// iterate all non-empty classes
				iter = seglist[i];

				while (iter) {
					if (FLAG(iter) == 1)	// simply check the flag of each block
						mm_error(2);			// if it's 'allocated', then error!
					iter = NEXTP(iter);
				}
			}
		break;
	case 2: /* Test2: Are there any contiguous free blocks that somehow escaped coalescing? */
		for (iter = heap_head; SIZE(iter) > 0; iter = NEXTB(iter)) {
			//printf("%d(%d) ", (VALUE(HEADER(iter))), (VALUE(HEADER(iter))) & 0x1);
			if (first_flag == 1) {			// only for the first step of iteration 
				if (FLAG(iter) == 0)
					prev_f_flag = 1;		// intermediate state for error situation
				else prev_f_flag = 0;

				first_flag = 0;
			}
			else {
				if (FLAG(iter) == 0) {
					if (prev_f_flag == 0)
						prev_f_flag = 1;
					else mm_error(3);		// when two consecutive blocks are freed!
				}
				else prev_f_flag = 0;
			}
		}
		break;
	case 3: /* Test3: Is every free block actually in the free list? */
		for (iter = heap_head; SIZE(iter) > 0; iter = NEXTB(iter)) {
			if (FLAG(iter) == 0) {					// for every free blocks in heap,
				index = what_class(SIZE(iter));		// specify the corresponding class,
				//printf("[%d]%d(%d) : ", index, (VALUE(HEADER(iter))), (VALUE(HEADER(iter))) & 0x1);
				jter = seglist[index];
				found = 0;

				while (jter) {						// and then traverse that class,
					if (iter == jter)
						found++;					// count whenever u find the same address of block
					//printf("%d(%d), ", (VALUE(HEADER(jter))), (VALUE(HEADER(jter))) & 0x1);
					jter = NEXTP(jter);
				}

				if (found != 1) mm_error(4);	// count must be NOT ONLY nonzero, but also must be 1
			}
		}
		break;
	case 4: /* Test4: Do the pointers in the free list point to valid free blocks? */
		for (i = 0; i < CLASSES; i++)
			if (seglist[i] != NULL) {
				iter = seglist[i];

				while (iter) {			// simply check the connection state!
					if ((NEXTP(iter) != NULL) && (iter != PREVP(NEXTP(iter))))
						mm_error(5);
					if ((PREVP(iter) != NULL) && (iter != NEXTP(PREVP(iter))))
						mm_error(5);

					iter = NEXTP(iter);
				}
			}
		break;
	case 5: /* Test5: Do any allocated blocks overlap? */
		for (iter = NEXTB(heap_head); SIZE(iter) > 0; iter = NEXTB(iter)) {
			if (FLAG(iter) == 1) {			// for every allocated blocks,
				next = NEXTB(iter);

				if (SIZE(next) > 0 && FLAG(next) == 1) {	// if next is also allocated,
					size = SIZE(iter);

					jter = HEADER(iter);
					byte_cnt = 0;
					while (jter != HEADER(next)) {		// then check the overlap!
						jter = (char *)jter + 1;			// go forward by 'BYTE'
						byte_cnt++;							// count bytes number
					}

					if (byte_cnt != size)		// check if bytes number matches cur_size
						mm_error(6);
				}
			}
		}
		break;
	case 6: /* Test6: Do the pointers in a heap block point to valid heap addresses? */
		for (iter = NEXTB(heap_head); (VALUE(HEADER(iter)) & ~0x7) > 0; iter = NEXTB(iter)) {
			if ((NEXTB(iter) != NULL) && (iter != PREVB(NEXTB(iter))))
				mm_error(7);
			if ((PREVB(iter) != NULL) && (iter != NEXTB(PREVB(iter))))
				mm_error(7);
		}		// simply check the connection state!
		break;
	case 7: /* Test7(self): Print the heap word by word, and the whole free lists!
		with checking whether each blocks in the heap is aligned by doublewords. */
		iter = NEXTB(heap_head);

		while (SIZE(iter) > 0) {	// for every blocks in heap (regardless of flag)
			if ((size_t)iter % DWORD != 0)		// check the alignment
				mm_error(8);

			size = SIZE(iter) / WORD;
			total_size += (size * 4);
			byte_cnt = 0;

			printf("| ");
			for (jter = HEADER(iter), i = 0; i < size;	// iterate the inside of block
				jter = (char *)jter + WORD, i++) {
				if (FLAG(iter) == 1) {					// if block is allocated,
					if (i == 0) printf("ah(4) ");
					else if (i == size - 1) printf("p(%d) af(4) ", byte_cnt * 4);
					else byte_cnt++;
				}
				else {
					if (i == 0) printf("fh(4) ");		// if block is freed,
					else if (i == 1 || i == 2) printf("fp(4) ");
					else if (i == size - 1) printf("p(%d) ff(4) ", byte_cnt * 4);
					else byte_cnt++;
				}
			}

			iter = NEXTB(iter);
		}
		printf("|\nTotal: %d Bytes\n", total_size);		// total bytes of heap

		for (i = 0; i < CLASSES; i++) {
			if (seglist[i] != NULL) {
				iter = seglist[i];			// print all the non-empty seglist classes
				printf("Class %d: ", i);

				while (iter) {
					printf("%d ", SIZE(iter));

					iter = NEXTP(iter);
				}
				printf("\n");
			}
		}
		printf("\n");
		break;
	default: break;
	}

	return 0;
}
/****    End of Subroutines for interfaces    ****/