/* -*- swig -*- */
/* SWIG interface file to create the Java API for OpenSMT2  */

%include "enums.swg"
%javaconst(1);

%include "typemaps.i"

%module opensmt2java
%{

  #include "opensmt_c.h"

  //#include "/home/lubuntu/SAHEED/gsoc/opensmt2java/opensmt/src/api/opensmt_c.h"

  /*
  int givenum(int num){

  //char str[50];
  //sprintf(str, "%i", num); 
    
  return num;
 }

  */
  
  %}

  %include "opensmt_c.h"

//%include "/home/lubuntu/SAHEED/gsoc/opensmt2java/opensmt/src/api/opensmt_c.h"

//int givenum(int);
