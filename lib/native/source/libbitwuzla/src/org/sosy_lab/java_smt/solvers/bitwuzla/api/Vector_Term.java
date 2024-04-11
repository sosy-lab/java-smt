/* ----------------------------------------------------------------------------
 * This file was automatically generated by SWIG (https://www.swig.org).
 * Version 4.1.0
 *
 * Do not make changes to this file unless you know what you are doing - modify
 * the SWIG interface file instead.
 * ----------------------------------------------------------------------------- */

package org.sosy_lab.java_smt.solvers.bitwuzla.api;

public class Vector_Term extends java.util.AbstractList<Term> implements java.util.RandomAccess {
  private transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  protected Vector_Term(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(Vector_Term obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected static long swigRelease(Vector_Term obj) {
    long ptr = 0;
    if (obj != null) {
      if (!obj.swigCMemOwn)
        throw new RuntimeException("Cannot release ownership as memory is not owned");
      ptr = obj.swigCPtr;
      obj.swigCMemOwn = false;
      obj.delete();
    }
    return ptr;
  }

  @SuppressWarnings("deprecation")
  protected void finalize() {
    delete();
  }

  public synchronized void delete() {
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        //BitwuzlaNativeJNI.delete_Vector_Term(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public Vector_Term(Term[] initialElements) {
    this();
    reserve(initialElements.length);

    for (Term element : initialElements) {
      add(element);
    }
  }

  public Vector_Term(Iterable<Term> initialElements) {
    this();
    for (Term element : initialElements) {
      add(element);
    }
  }

  public Term get(int index) {
    return doGet(index);
  }

  public Term set(int index, Term e) {
    return doSet(index, e);
  }

  public boolean add(Term e) {
    modCount++;
    doAdd(e);
    return true;
  }

  public void add(int index, Term e) {
    modCount++;
    doAdd(index, e);
  }

  public Term remove(int index) {
    modCount++;
    return doRemove(index);
  }

  protected void removeRange(int fromIndex, int toIndex) {
    modCount++;
    doRemoveRange(fromIndex, toIndex);
  }

  public int size() {
    return doSize();
  }

  public Vector_Term() {
    this(BitwuzlaNativeJNI.new_Vector_Term__SWIG_0(), true);
  }

  public Vector_Term(Vector_Term other) {
    this(BitwuzlaNativeJNI.new_Vector_Term__SWIG_1(Vector_Term.getCPtr(other), other), true);
  }

  public long capacity() {
    return BitwuzlaNativeJNI.Vector_Term_capacity(swigCPtr, this);
  }

  public void reserve(long n) {
    BitwuzlaNativeJNI.Vector_Term_reserve(swigCPtr, this, n);
  }

  public boolean isEmpty() {
    return BitwuzlaNativeJNI.Vector_Term_isEmpty(swigCPtr, this);
  }

  public void clear() {
    BitwuzlaNativeJNI.Vector_Term_clear(swigCPtr, this);
  }

  public Vector_Term(int count, Term value) {
    this(BitwuzlaNativeJNI.new_Vector_Term__SWIG_2(count, Term.getCPtr(value), value), true);
  }

  private int doSize() {
    return BitwuzlaNativeJNI.Vector_Term_doSize(swigCPtr, this);
  }

  private void doAdd(Term x) {
    BitwuzlaNativeJNI.Vector_Term_doAdd__SWIG_0(swigCPtr, this, Term.getCPtr(x), x);
  }

  private void doAdd(int index, Term x) {
    BitwuzlaNativeJNI.Vector_Term_doAdd__SWIG_1(swigCPtr, this, index, Term.getCPtr(x), x);
  }

  private Term doRemove(int index) {
    return new Term(BitwuzlaNativeJNI.Vector_Term_doRemove(swigCPtr, this, index), true);
  }

  private Term doGet(int index) {
    return new Term(BitwuzlaNativeJNI.Vector_Term_doGet(swigCPtr, this, index), false);
  }

  private Term doSet(int index, Term val) {
    return new Term(BitwuzlaNativeJNI.Vector_Term_doSet(swigCPtr, this, index, Term.getCPtr(val), val), true);
  }

  private void doRemoveRange(int fromIndex, int toIndex) {
    BitwuzlaNativeJNI.Vector_Term_doRemoveRange(swigCPtr, this, fromIndex, toIndex);
  }

}