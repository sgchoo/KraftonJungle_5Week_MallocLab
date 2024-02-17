/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define MAX(x, y)           ((x) > (y)? (x) : (y))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT           8 // 할당하는 단위

/* Basic constants and macros */
#define WSIZE               4       /* Word and header.footer size (1bytes) */
#define DSIZE               8       /* Double word size (2bytes) */
#define CHUNKSIZE           (1<<12) /* 4Kb (데이터 섹터 크기) */

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size)         (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE         (ALIGN(sizeof(size_t)))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (size_t)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NEXT_FBLKP(bp)      ((bp))
#define PREV_FBLKP(bp)      ((bp+4))

static char *heap_listp;
static list_t free_list;

static void *coalesce(void *bp)
{
    // printf("@@@ %p\n", free_list.end);
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전블럭이 할당되어있는지 여부를 확인하는 변수
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음블럭
    size_t size = GET_SIZE(HDRP(bp));
    printf("coalesce, %p \n", bp);
    /* case 1: */
    if (prev_alloc && next_alloc)
    {
        // printf("!!\n");
        if (free_list.end != free_list.start) {
            if (bp < free_list.start) {
                // 다음 노드의 prev를 나로 변경
                PUT(PREV_FBLKP(free_list.start), bp);
                // 지금 노드의 next에 다음노드 주소 저장
                PUT(NEXT_FBLKP(bp),free_list.start);
                //start를 나로
                free_list.start=bp;
                // 시작 노드의 prev는  end로 써클연결 monster
                PUT(PREV_FBLKP(bp),free_list.end);
            }
            else if (bp > free_list.end) {
                // printf("!!!!!!!!!\n");
                // 이전 노드의 next를 나로 변경
                PUT(NEXT_FBLKP(free_list.end), bp);
                // 지금 노드의 prev에 이전노드 주소 저장
                PUT(PREV_FBLKP(bp),free_list.end);
                //end를 나로
                free_list.end=bp;
                // 마지막 노드의 next는 시작점으로 써클연결 monster
                PUT(NEXT_FBLKP(bp),free_list.start);
            }
            else  {
                // printf("!!!\n");
                PUT(NEXT_FBLKP(PREV_FBLKP(bp)) , bp);
                PUT(PREV_FBLKP(NEXT_FBLKP(bp)) , bp);
                // 여기 
                PUT(NEXT_FBLKP(bp), NEXT_BLKP(bp));
                PUT(PREV_FBLKP(bp), PREV_BLKP(bp)); 
            }
        }
        return bp;
    }
    /* case 2: */
    else if (prev_alloc && !next_alloc) 
    {
        // printf("!!\n");
        char *next = NEXT_BLKP(bp);

        if (bp < free_list.start) {
            // 여기
            PUT(NEXT_FBLKP(bp), NEXT_FBLKP(next));
            PUT(PREV_FBLKP(bp), PREV_FBLKP(next));
            free_list.start = bp;
            PUT(NEXT_FBLKP(free_list.end), bp);
        }
        else {
            //여기
            PUT(NEXT_FBLKP(bp), NEXT_FBLKP(next));
            PUT(PREV_FBLKP(bp), PREV_FBLKP(next));
        }
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }
    /* case 3: */
    else if (!prev_alloc && next_alloc) 
    {
        // printf("!!\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* case 4: */
    else
    {
        if (NEXT_BLKP(bp) == free_list.end)
            free_list.end = PREV_BLKP(bp);
        PUT(NEXT_FBLKP(PREV_BLKP(bp)), NEXT_FBLKP(NEXT_BLKP(bp)));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment*/
    size = (words % 2) ? (words+1) * WSIZE : words *WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;


    /* Initialize free block header/footer and the epilogue header*/
    PUT(HDRP(bp), PACK(size,0));    /* Free block header*/
    // 
    PUT(FTRP(bp), PACK(size,0));    /* Free block footer*/
    // printf("%p %p \n", bp, PREV_FBLKP(bp));
    PUT(NEXT_FBLKP(bp), 1);     /*다음 프리블럭 포인터*/
    PUT(PREV_FBLKP(bp), 1);     /* 이전 프리블럭 포인터*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /* New epilogue header*/

    /* case 1 : 처음이면*/
    if (free_list.start ==NULL && free_list.end == NULL) {
        free_list.start=free_list.end=bp;
        PUT(NEXT_FBLKP(bp), bp);
        PUT(PREV_FBLKP(bp), bp);
    }
    /* case 2 : 다음에 가용할 리스트가 있다면?*/

    return coalesce(bp);  //코올레스

}

static void *find_fit(size_t adjust_size)
{
    // /* First-fit search*/
    // void *bp;
    // //printf("너니??");
    // for (bp = heap_listp ; GET_SIZE(HDRP(bp)) > 0 ; bp = NEXT_BLKP(bp))
    // {
    //     //printf("너니");
    //     if(!GET_ALLOC(HDRP(bp)) && (adjust_size <= GET_SIZE(HDRP(bp))))
    //     {
            
    //         return bp;
    //     }
    // }
    // return NULL; /* No fit */

    /* New search*/
    char *next=free_list.start;


    do {
        if(adjust_size <= GET_SIZE(HDRP(next))) {
            return next;
        }
        next = NEXT_FBLKP(next);
    } while (next != free_list.end);
    
    return NULL;
}

static void place(void *bp, size_t adjust_size)
{
    size_t cur_size = GET_SIZE(HDRP(bp));

    if ((cur_size - adjust_size) >= (2*DSIZE))
    {   
        printf("남는 공간 충분 place, %p \n", bp);
        PUT(HDRP(bp), PACK(adjust_size, 1));
        PUT(FTRP(bp), PACK(adjust_size, 1));
        bp=NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(cur_size - adjust_size, 0));
        PUT(FTRP(bp), PACK(cur_size - adjust_size, 0));
        
        // 프리 블록 재생성 -> 프리 블록에게 앞뒤 블록 연결
        // 빈 블록이 하나일 때 
        if (free_list.start == PREV_BLKP(bp) && free_list.end == PREV_BLKP(bp)) {
            printf("1!!!!!\n");
            free_list.start = bp;
            free_list.end = bp;
            printf("place%p\n" ,bp);

        }
        // if 스타트 지점을 옮겨야 할 때
        else if (free_list.start == PREV_BLKP(bp)) {
            printf("2!!!!!\n");
            free_list.start = bp;
        }
        // if 엔드 지점을 옮겨야 할 때
        else if (free_list.end == PREV_BLKP(bp)) {
            printf("3!!!!!\n");
            free_list.end = bp;
        }

        PUT(PREV_FBLKP(bp), NEXT_FBLKP(PREV_BLKP(bp)));
        PUT(NEXT_FBLKP(bp), PREV_FBLKP(NEXT_BLKP(bp)));

        PUT(PREV_FBLKP(NEXT_FBLKP(bp)), bp);
        PUT(NEXT_FBLKP(PREV_FBLKP(bp)), bp);
    }
    else
    {
        // 프리 블록 삭제됨 -> 앞뒤 프리 블록 서로 연결
        printf("남는 공간 부족 place, %p \n", bp);
        PUT(HDRP(bp), PACK(cur_size, 1));
        PUT(FTRP(bp), PACK(cur_size, 1));
        if (free_list.start == bp && free_list.end == bp) {
            free_list.end = NULL;
            free_list.start = NULL;
        } else {
            PUT(PREV_FBLKP(bp), NEXT_FBLKP(bp));
            PUT(NEXT_FBLKP(bp), PREV_FBLKP(bp));
        }
    }

}



/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap*/
    free_list.start = NULL;
    free_list.end = NULL;
    
    if ((heap_listp = mem_sbrk(4*WSIZE))== (void *)-1)
        return -1;
    PUT(heap_listp,0);  /*Alignment padding*/
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); /* Prologue header*/
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); /* Prologue footer*/
    PUT(heap_listp + (3*WSIZE), PACK(0,1));  /* Epilogue header*/
    heap_listp += (2*WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    //printf("afafafdf");
  size_t adjust_size; /* Adjusted(조정가능한) block size*/
  size_t extend_size; /* Amount to extend heap if no fit */
  char *bp;

    printf("size = %d\n", size);
  /* Ignore spurious requests*/
  // 미친 테케용
  if (size == 0)
    return NULL;

  /* Adjust block size to include overhead(h&f) and alignment reqs. */
  if (size <=DSIZE)
    adjust_size = 2*DSIZE;
  else{
    //  adjust_size = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    //  printf("%d %d\n",adjust_size, size);
    adjust_size = ALIGN(size)+8;  //헤더푸터 추가해줘야되니까 8byte 추가
  }

  /* Search the free list for a fit  중요한 부분 */
  if ((bp = find_fit(adjust_size)) != NULL)
  {
    printf("find fit, %p %p\n", free_list.start, bp);
    //printf("!!!");
    place(bp, adjust_size);
    return bp;
  }
  /* No fit found. Get more memory and place the block*/
  printf("Extend heap \n");
  extend_size = MAX(adjust_size, CHUNKSIZE);
  if ((bp = extend_heap(extend_size/WSIZE)) == NULL){
    return NULL;
  }
  //printf("!!!!!");
  place(bp, adjust_size);
  return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp),PACK(size, 0));
    PUT(FTRP(bp),PACK(size, 0));
    if (free_list.end == NULL && free_list.start == NULL) {
        free_list.start = bp;
        free_list.end = bp;
    }
    else {
        
    }
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;
    void *newptr;
    size_t copy_size;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    // copy_size = *(size_t *)((char *)oldptr - WSIZE) - 9;
    copy_size = (size_t)(GET_SIZE(HDRP(oldptr))) - DSIZE;
     //copy_size = *(size_t *)((char *)oldptr - SIZE_T_SIZE); //
    if (size < copy_size)
      copy_size = size;
    memcpy(newptr, oldptr, copy_size);
    mm_free(oldptr);
    return newptr;
}