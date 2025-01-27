# Specification

## Introduction

We denote partial functions from $A$ to $B$ as $A \rightharpoonup B$.

- Syntax
	- Variables $x$
	- Integer literals $n$
	- Expressions $e$
	- Tags $T$
	- Labels $\ell$
	- Types $\tau$
	- Kinds $\kappa$
- Environments
	- Typing $\Gamma : x \rightharpoonup \tau$
- Judgements
	- Subtyping $\tau \sqsubseteq \tau$
	- Typing $\Gamma \vdash e : \tau$

Unless specified otherwise, types have the the kind $\star$.

> Quote blocks – like this one – are side notes, which might be somewhat out of context.

### Subtyping

We define subtyping $\sqsubseteq$ in terms of the distributive bounded lattice $(\tau, \sqcap, \sqcup, \bot, \top)$, defining the key equalities. Note that $\sqcup$/$\top$ are dual to $\sqcap$/$\bot$.
Under subtyping, we have the key implicit coercion rule:

$$ \dfrac{\Gamma \vdash e : \tau \quad \tau \sqsubseteq \tau'}{\Gamma \vdash e : \tau'}  $$

## Primitives
### Integers

Integers are signed, with an implementation-defined size. We have some set of convenient integer operators $\oplus$.

$$ e ::= n \mid e \oplus e \quad \tau ::= \cdots \mid \mathrm{int} $$

> For WebAssembly this might be 31 bits, so that they represented uniformly as a pointer-sized value. This is sufficient for basic operations and for use as array indices.

## Functions

We have the usual abstraction type judgements.

$$ e ::= \cdots \mid (x : \tau) \Rightarrow e \mid e\,e \quad \tau ::= \cdots \mid \tau \to \tau  $$
$$ (\tau_1 \to \tau_2) \sqcap (\tau_1' \to \tau_2') = (\tau_1 \sqcup \tau_1') \to (\tau_2 \sqcap \tau_2') $$

> We posit the meet on function types as in MLstruct (and it seems analogical to MLsub) though – as noted there – it does not fit a set-theoretic interpretation of function types.

## Products

Tuples of different arities are unrelated.

$$ e ::= \cdots \mid (\overrightarrow{e_i}) \quad \tau ::= \cdots \mid (\overrightarrow{\tau_i}) \quad (\overrightarrow{\tau_i}) \sqcap (\overrightarrow{\pi_i}) = (\overrightarrow{\tau_i \sqcap \pi_i}) $$
 
 Tuples can only be unpacked in a context where their arity is known. 

## Records

> We write $\overrightarrow{\sigma}$ for a list across some index $i$.

Record types are partial functions from labels $\ell$ to pairs of types $\tau$ and *frames* $f$, i.e. $\ell \rightharpoonup (\tau, f)$. 
Frames also form a lattice, and describe the kind of a field. Thus we have a product lattice $(\tau, f)$. The frame can be omitted, leaving it either free or defaulting to $\texttt{present}$.

$$ e ::= \cdots \mid  \{ \overrightarrow{\ell_i: e_i} \} \mid e{.}\ell \qquad \tau ::= \cdots \mid \{ \overrightarrow{\ell_i \triangleright f_i : \tau_i} \} \qquad f ::= \texttt{present} $$
 $$ \dfrac{\Gamma \vdash \overrightarrow{e_i : \tau_i}}{\Gamma \vdash \{ \overrightarrow{\ell_i : e_i} \}  : \overrightarrow{\ell_i : \tau_i}} \qquad \dfrac{\Gamma \vdash e : \{ \ell \triangleright \texttt{present} : \tau \}}{\Gamma \vdash e{.}\ell : \tau } $$
 $$ \{ \overrightarrow{r_1} \} \sqcap \{ \overrightarrow{r_2} \} = \{ \ell : r_1(\ell) \sqcap r_2(\ell) \mid \ell \in r_1 \lor \ell \in r_2 \} $$ 
> It would be nice for *frames* to fit the abstraction of optional and perhaps absent fields (i.e. ones suitable for record extension). 
> It’d be also nice to have mutable records behave for records, too, but there’s some difficulties with inference. This would be interesting, and there’s hints in Chapter 9 of Dolan’s thesis.

## Variants

> Dolan proposes sums-of-products as a single type (‘tagged records’). But are these actually better? Perhaps it’s sufficient to have bounded records/variants and a primitive that extracts underlying data?

$$ e ::= \cdots \mid \mathrm{case}\,e\,\mathrm{of}\,\overrightarrow{T_i\,x_i \Rightarrow e_i} \mid T\, e \qquad \tau ::= \cdots \mid [T_1: \tau_1, \cdots, T_k : \tau_k] $$
$$ \dfrac{\Gamma \vdash e : [\overrightarrow{T_i\,x_i : \tau_i}] \quad \overrightarrow{\Gamma, x_i : \tau_i \vdash e_i : \tau}}{\Gamma \vdash \mathrm{case}\,e\,\mathrm{of}\,\overrightarrow{T_i\,x_i \Rightarrow e_i} : \tau} \quad \dfrac{\Gamma \vdash e : \tau}{\Gamma \vdash T\, e : [ T: \tau]} $$ $$ [ \overrightarrow{r_1}] \sqcap [\overrightarrow{r_2}] = \{ \ell : r_1(\ell) \sqcap r_2(\ell) \mid \ell \in r_1 \land \ell \in r_2 \} $$
 
## Arrays

> Only immutable, single-dimensional arrays for now.

$$ e ::= \cdots \mid [ x : e] \Rightarrow e \mid e[e] \mid \mathrm{shape}\,e \quad \tau ::= \cdots \mid \Box \tau $$
$$ \dfrac{\Gamma,x : \mathrm{int} \vdash e : \tau \quad \Gamma \vdash e' : \mathrm{int}}{\Gamma \vdash [x : e'] \Rightarrow e : \Box \tau} \quad 
\dfrac{\Gamma \vdash e : \Box \tau \quad \Gamma \vdash e' : \mathrm{int}}{\Gamma \vdash e : \tau} \quad 
\dfrac{\Gamma \vdash e : \Box \tau}{\Gamma \vdash \mathrm{shape}\,e : \mathrm{int}} $$ 

Defining an array of negative size or indexing an array out of bounds is implementation-defined. Arrays initialised with $[x : n] \Rightarrow e$ yield $(\{0/x\}e, \cdots, \{n-1/x\}e)$ indexed from $0$ to $n - 1$.

>  The idea has been that $\Box$ should instead stand for some sort of shape, with shapes forming an algebra over products (multiple dimensions) and sums (concatenations). These products and sums could be named, in which case indexing would use records and variants.

## Extensions

These are rough sketches of *interesting* modifications of the above type system.
They would form research contributions.

### Structured arrays

==TODO== 

### Bounded records & variants

$[\diamond : \tau]$ indicates a *bounded variant* – one for which every tag’s data is of type $\tau$.

$$ e ::= \cdots \mid \mathrm{untag} \,e \quad \tau ::= \cdots \mid [\diamond : \tau] $$
$$ [\diamond : \tau] \sqcap [\diamond : \tau'] = [\diamond : \tau \sqcap \tau'] \qquad [\diamond : \tau] \sqcap [\overrightarrow{T_i : \tau_i}] = [\overrightarrow{T_i : \tau \sqcap \tau_i}] $$
$$ \dfrac{\Gamma \vdash e : [\diamond : \tau]}{\Gamma \vdash \mathrm{untag}\,e : \tau} $$ 

> I show just the example of variants. The construction is dual for records (?), but it is not obvious what the elimination form should be (reduction with a commutative monoid over all fields?).
> Both bounded variants and bounded records eliminate boilerplate. For variants, we might have $n$ cases of terms with record data where each has some field with a label $\mathrm{location}$ - Dolan’s example. For records, we might be able to generate a printing or hashing function.

### Properties

> Notes: [[Properties in Fabric]].

> This is a simple version of properties, with $p$ a set of property names $\ell$. I believe they could be made more nuanced and closer to usual types $\tau$. Crucially, properties $p$ shall form a lower-bounded semilattice $(\varnothing, \sqcup)$.

$e \Uparrow p$ gives $e$ the property $p$, while $e \Downarrow p$ only type-checks of $e$ with this property.
Thus, $(e \Uparrow p) \Downarrow p$ is always accepted, but $(e \Downarrow p) \Uparrow p$ checks iff $e \Downarrow p$ does.

$$ e ::= \cdots \mid e \Uparrow p \mid e \Downarrow p \mid \mathrm{rule}\,p\vdash p \,\mathrm{in}\,e  $$ 

We add the *property judgement* $\Pi; R \vdash e \Rightarrow p$, a property environment $\Pi : x \rightharpoonup p$ and rule environment (given as a relation) $R \subseteq p \times p$. Crucially, we have the property-inference rule that builds up proofs of properties implicitly using the available rules:

$$ \dfrac{\Pi; R \vdash e \Rightarrow p \quad p\,R\,p'}{\Pi; R \vdash e \Rightarrow p'} $$

We need some scaffolding (subtyping, environment):

$$ \dfrac{\Pi; R \vdash e \Rightarrow p \quad p\,\sqsubseteq p'}{\Pi; R \vdash e \Rightarrow p'} \qquad \dfrac{\Pi(x) = p}{\Pi; R \vdash x \Rightarrow p}$$

And bestow the following rules on the available expressions:

$$ \dfrac{\Pi; R \vdash e \Rightarrow p}{\Pi; R \vdash e \Uparrow p' \Rightarrow p \sqcup p'} \quad
\dfrac{\Pi; R \vdash e \Rightarrow p}{\Pi; R \vdash e \Downarrow p \Rightarrow p} \quad
\dfrac{\Pi; R, (p', p'') \vdash e \Rightarrow p}{\Pi; R \vdash \mathrm{rule}\,p' \vdash p''\,\mathrm{in}\,e} $$

### Nominal types

> Notes: [[Nominal types in Fabric]]

We introduce type abbreviations $t$, and an abbreviation environment $\Lambda$. 

$$ e ::= \cdots \mid \mathrm{abbrev}\,t = \tau\,\mathrm{in}\,e \mid e :\succ \tau \mid e : \tau :\succ \tau \qquad \tau ::= \cdots \mid t $$ 
$$ \mathrm{expand}_\Lambda(t) = \Lambda(t) \qquad \mathrm{expand}_\Lambda(T(\overrightarrow{\tau_i})) = T\left(\overrightarrow{\mathrm{expand}_\Lambda(\tau_i)}\right) $$
$$ \dfrac{\Gamma; \Lambda, t: \tau \vdash e : \tau'}{\Gamma; \Lambda \vdash \mathrm{abbrev} \,t = \tau\, \mathrm{in}\, e : \tau'} $$
$$ \dfrac{\Gamma; \Lambda \vdash e : \mathrm{expand}_\Lambda(\tau)}{\Gamma; \Lambda : e :\succ \tau : \tau} \quad
\dfrac{\Gamma; \Lambda \vdash e : \tau \quad \tau \equiv_{\mathrm{expand}_\Lambda} \tau'}{\Gamma; \Lambda : (e : \tau :\succ \tau') : \tau'} $$

Note that $e :\succ \tau$ is effectively an alias for $e : \tau :\succ \tau$ – abbreviate everything and expand nothing. The idea of the additional annotation is to provide the source type for the abbreviation, allowing the type checker to insert the appropriate constraint, and providing a witness the we can expand/abbreviate along to $\tau’$ (we compare abbreviation-free normal forms under $\mathrm{expand}_\Lambda$).

> $\mathrm{expand}$ propagates functorially down type constructors, replacing known abbreviations with their expansions, and preserving other abbreviation names (→ abstraction).
> This is tricky, because for polymorphism we need to have an environment for type variables. Let us just assume there is some well-formedness judgement for $\tau$.

Abbreviations $t$ are unrelated to all other abbreviations $t’ \ne t$, i.e. $t \sqcap t’ = \bot$. They are also unrelated to their expansion, and can only be coerced.

### Unboxed types

We extend the kind system with:

$$ \kappa ::= \star \mid \mathrm{i32} \mid \mathrm{i64} \mid \mathrm{f32} \mid \mathrm{f64} $$

And fix all existing type constructors to be on $\star$, except functions, which are polymorphic in the kind and yield different instantiations. Could attempt kind polymorphism afterwards.

#### Unboxed tuples

$$ \kappa ::= \cdots \mid \langle \overrightarrow{\kappa_i} \rangle $$

==TODO== 

### Frames for record fields

> Notes: [[Record frames in Fabric]]

==TODO== 

