package org.sosy_lab.solver.api;

/**
 * Declaration of function.
 */
public class Declaration {
  private final String name;
  private final DeclarationKind kind;

  private Declaration(String name, DeclarationKind kind) {
    this.name = name;
    this.kind = kind;
  }

  public static Declaration of(String name, DeclarationKind kind) {
    return new Declaration(name, kind);
  }

  /**
   * Get type of the declaration.
   */
  public DeclarationKind getKind() {
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
}
