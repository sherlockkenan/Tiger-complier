/*
 * util.c - commonly used utility functions.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include "util.h"
void *checked_malloc(int len)
{void *p = malloc(len);
 if (!p) {
    fprintf(stderr,"\nRan out of memory!\n");
    exit(1);
 }
 return p;
}
void *checked_realloc(void *p, size_t size)
{
	void *ptr = realloc(p, size);
	if (!ptr) {
		fprintf(stderr, "\nRand out of memory (realloc)!\n");
		exit(1);
	}
	return ptr;
}

string String(char *s)
{string p = checked_malloc(strlen(s)+1);
 strcpy(p,s);
 return p;
}

static string simple_itoa(int n,int radix){
  string buf = checked_malloc(INITSIZE);
  if(radix==10){
    sprintf(buf,"%d",n);
  }else if(radix==16){
    sprintf(buf,"%x",n);
  }else{
    assert(0);
  }
  return buf;
}

string string_format(const string format,...){
  string buf = checked_malloc(INITSIZE);
  int bufSize = INITSIZE;
  const char *slice = NULL;
  char* curPos = format;
  int size = 0,sliceSize=0;//size:size of
  va_list ap;
  va_start(ap,format);
  while(*curPos){
    if(*curPos=='%'){
      curPos++;
      if(*curPos=='d'){
        slice = simple_itoa(va_arg(ap,int),10);
      }else if(*curPos=='s'){
        slice = va_arg(ap,const char*);
      }else if(*curPos=='x'){
        slice = simple_itoa(va_arg(ap,int),16);
      }else{
        assert(0);
      }
      sliceSize = strlen(slice);
    }
    else{
      slice = curPos;
      sliceSize = 1;
    }
    if(size+sliceSize>=bufSize){
      string tmp = checked_malloc(size*2+1);
      strncpy(tmp,buf,size);
      buf = tmp;
    }
    strncpy(buf+size,slice,sliceSize);
    size+=sliceSize;
    curPos++;
  }
  va_end(ap);
  return buf;
}

U_boolList U_BoolList(bool head, U_boolList tail)
{ U_boolList list = checked_malloc(sizeof(*list));
  list->head = head;
  list->tail = tail;
  return list;
}
