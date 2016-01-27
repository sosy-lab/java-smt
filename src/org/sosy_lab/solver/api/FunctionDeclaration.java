package org.sosy_lab.solver.api;

import com.google.common.base.Preconditions;

import java.util.Objects;

import javax.annotation.Nullable;

/**
 * Declaration of function.
 */
public class FunctionDeclaration {
  private final String name;
  private final FunctionDeclarationKind kind;

  private FunctionDeclaration(String name, FunctionDeclarationKind kind) {
    Preconditions.checkNotNull(name);
    Preconditions.checkNotNull(kind);
    this.name = name;
    this.kind = kind;
  }

  public static FunctionDeclaration of(String name, FunctionDeclarationKind kind) {
    return new FunctionDeclaration(name, kind);
  }

  /**
   * Get type of the declaration.
   */
  public FunctionDeclarationKind getKind() {
    return kind;
  }

  /**
   * Name of the function.
   * For variables and UF's, it's the user-supplied name.
   * For default theories, it is the operator name (e.g. {@code "ITE"} for the
   * if-then-else operator.)
   */
  public String getName() {
    return name;
  }

  @Override
  public String toString() {
    return String.format("%s (%s)", kind, name);
  }

  @Override
  public int hashCode() {
    return Objects.hash(kind, name);
  }

  @Override
  public boolean equals(@Nullable Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof FunctionDeclaration)) {
      return false;
    }
    FunctionDeclaration other = (FunctionDeclaration) o;
    return (name.equals(other.name) && kind.equals(other.kind));
  }
}
