// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/* ----------------------------------------------------------------------------
 * This file was automatically generated by SWIG (https://www.swig.org).
 * Version 4.1.1
 *
 * Do not make changes to this file unless you know what you are doing - modify
 * the SWIG interface file instead.
 * ----------------------------------------------------------------------------- */

package org.sosy_lab.java_smt.solvers.bitwuzla.api;

public class Vector_Int extends java.util.AbstractList<Integer> implements java.util.RandomAccess {
  private transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  protected Vector_Int(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(Vector_Int obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected static long swigRelease(Vector_Int obj) {
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
        BitwuzlaNativeJNI.delete_Vector_Int(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public Vector_Int(int[] initialElements) {
    this();
    reserve(initialElements.length);

    for (int element : initialElements) {
      add(element);
    }
  }

  public Vector_Int(Iterable<Integer> initialElements) {
    this();
    for (int element : initialElements) {
      add(element);
    }
  }

  public Integer get(int index) {
    return doGet(index);
  }

  public Integer set(int index, Integer e) {
    return doSet(index, e);
  }

  public boolean add(Integer e) {
    modCount++;
    doAdd(e);
    return true;
  }

  public void add(int index, Integer e) {
    modCount++;
    doAdd(index, e);
  }

  public Integer remove(int index) {
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

  public Vector_Int() {
    this(BitwuzlaNativeJNI.new_Vector_Int__SWIG_0(), true);
  }

  public Vector_Int(Vector_Int other) {
    this(BitwuzlaNativeJNI.new_Vector_Int__SWIG_1(Vector_Int.getCPtr(other), other), true);
  }

  public long capacity() {
    return BitwuzlaNativeJNI.Vector_Int_capacity(swigCPtr, this);
  }

  public void reserve(long n) {
    BitwuzlaNativeJNI.Vector_Int_reserve(swigCPtr, this, n);
  }

  public boolean isEmpty() {
    return BitwuzlaNativeJNI.Vector_Int_isEmpty(swigCPtr, this);
  }

  public void clear() {
    BitwuzlaNativeJNI.Vector_Int_clear(swigCPtr, this);
  }

  public Vector_Int(int count, int value) {
    this(BitwuzlaNativeJNI.new_Vector_Int__SWIG_2(count, value), true);
  }

  private int doSize() {
    return BitwuzlaNativeJNI.Vector_Int_doSize(swigCPtr, this);
  }

  private void doAdd(int x) {
    BitwuzlaNativeJNI.Vector_Int_doAdd__SWIG_0(swigCPtr, this, x);
  }

  private void doAdd(int index, int x) {
    BitwuzlaNativeJNI.Vector_Int_doAdd__SWIG_1(swigCPtr, this, index, x);
  }

  private int doRemove(int index) {
    return BitwuzlaNativeJNI.Vector_Int_doRemove(swigCPtr, this, index);
  }

  private int doGet(int index) {
    return BitwuzlaNativeJNI.Vector_Int_doGet(swigCPtr, this, index);
  }

  private int doSet(int index, int val) {
    return BitwuzlaNativeJNI.Vector_Int_doSet(swigCPtr, this, index, val);
  }

  private void doRemoveRange(int fromIndex, int toIndex) {
    BitwuzlaNativeJNI.Vector_Int_doRemoveRange(swigCPtr, this, fromIndex, toIndex);
  }

}
