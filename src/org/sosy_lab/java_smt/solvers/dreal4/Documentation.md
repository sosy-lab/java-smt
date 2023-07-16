#### Fragen:
- Soll jetzt nur noch mit Pointer gearbeitet werden oder sollen auch die interface Klassen 
  verwendet werden? -> z.b TheoremProver mit Conifg und Context
- oder bei Dreal4Formula mit toString Methode

- Not in BooleanFormulaManager


- UFManager, FormulaCreator welche Types?
- BooleanFormulaManger mit Variable erstellen von Typ Boolean und dann zu Formula umwandeln?
- Was sind die Types, bei BooleanFormulaManager bei ifThenElse, geht nur mit Expression

### SolverContext:
- newOptimizationProverEnvironment: man kann in config optimization wählen, vllt damit?


### DRealTerm
- eventuell Variable hinzufügen? Erstmal ohne probieren

### Not and negate:
- not bei BooleanFormula nur auf Formula? nur gucken, dass ganze formel nicht wahr wird?
- negate nur auf Variablen? Also nur Variable negieren


### FormulaManagers:
- Ich muss darauf achten, dass aus Variablen Expression erstellt werden können, um auch mit 
  Variables zu addieren usw.
- Gucken wie das mit erstellen von Variablen ist -> Expression oder Variable
- Überall wo Expression verwendet wird, kann auch Variable verwendet werden, vorher zu 
  Expression machen


- Equal(==) und iff das selbe in dREal bei Formals? und Equal(==) bei Variable oder Expression ist 
  dann x + 2 = 10
- Überladene Operatoren aufpassen, sind blöd


### Type:
- Type ist von Variable? Reicht das? Wir haben Boolean, Integer, Continous(double), Binary