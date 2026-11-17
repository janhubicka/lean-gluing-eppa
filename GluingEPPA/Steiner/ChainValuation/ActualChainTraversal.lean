import GluingEPPA.Steiner.ChainValuation.ChainTests
import GluingEPPA.Steiner.ChainValuation.ChainEndpointIterate
import GluingEPPA.Steiner.ChainValuation.WordAction
import GluingEPPA.Steiner.ChainValuation.CycleUnwindingCore

/-!
# A moved endpoint in the actual finite chain test

Read a word representing each block's specified outgoing displacement,
in the original block order.  Genuine matching edges take the identity
in the first block to the specified point of the last block.  If the
initial identity is outside the first attachment, it stays outside every
later block and is therefore moved by this word.

This is proved for the literal `buildNonempty` and `chainPerm`, including
their fixed-point completions.  Deriving the initial separation and the
identity value of this word from a coset cycle is a separate step.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {E : Type u} {X : Type v} {Y : Type w}

/-- A path which uses a genuine edge at every letter of its word. -/
def MatchingWordPath (P : E → Matching X) : List E → X → X → Prop
  | [], x, y => x = y
  | e :: rest, x, y => ∃ z, (P e).Rel x z ∧ MatchingWordPath P rest z y

theorem MatchingWordPath.append (P : E → Matching X)
    {p q : List E} {x y z : X}
    (hp : MatchingWordPath P p x y) (hq : MatchingWordPath P q y z) :
    MatchingWordPath P (p ++ q) x z := by
  induction p generalizing x with
  | nil =>
      change x = y at hp
      subst y
      exact hq
  | cons e p ih =>
      obtain ⟨t, hxt, ht⟩ := hp
      exact ⟨t, hxt, ih ht⟩

theorem MatchingWordPath.map (P : E → Matching X) (Q : E → Matching Y)
    (f : X → Y) (hf : ∀ e x y, (P e).Rel x y → (Q e).Rel (f x) (f y))
    {p : List E} {x y : X} (hp : MatchingWordPath P p x y) :
    MatchingWordPath Q p (f x) (f y) := by
  induction p generalizing x with
  | nil => exact congrArg f hp
  | cons e p ih =>
      obtain ⟨z, hxz, hz⟩ := hp
      exact ⟨f z, hf e x z hxz, ih hz⟩

theorem MatchingWordPath.completed (P : E → Matching X)
    {p : List E} {x y : X} (hp : MatchingWordPath P p x y) :
    EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
      (fun e => (P e).perm) p x = y := by
  induction p generalizing x with
  | nil => exact hp
  | cons e p ih =>
      obtain ⟨z, hxz, hz⟩ := hp
      change EdgeGraph.RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (P e).perm) p ((P e).perm x) = y
      rw [(P e).perm_eq_of_rel hxz]
      exact ih hz

theorem ChainState.last_word_path (B : GroupBlock E) (C : ChainState E B)
    (p : List E) (hp : ∀ e ∈ p, e ∈ B.active) (g : B.Carrier) :
    MatchingWordPath C.matching p
      (C.lastEmbed g) (C.lastEmbed (g * (p.map B.edge).prod)) := by
  induction p generalizing g with
  | nil => simp [MatchingWordPath]
  | cons e p ih =>
      have he : e ∈ B.active := hp e (by simp)
      have hrest : ∀ f ∈ p, f ∈ B.active := fun f hf => hp f (by simp [hf])
      refine ⟨C.lastEmbed (g * B.edge e), C.last_active e he g, ?_⟩
      simpa only [List.map_cons, List.prod_cons, mul_assoc] using
        ih hrest (g * B.edge e)

end GluingEPPA.Steiner.ChainValuation

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation

universe u v
variable {E : Type u} {X : Type v}

/-- The recursive test action agrees with the opposite permutation
product recorded by the augmented valuation. -/
theorem testWordPerm_eq_unop_product (τ : E → Equiv.Perm X) (word : List E) :
    testWordPerm τ word =
      MulOpposite.unop ((word.map (fun e => MulOpposite.op (τ e))).prod) := by
  induction word with
  | nil => rfl
  | cons e word ih =>
      change (τ e).trans (testWordPerm τ word) =
        MulOpposite.unop (MulOpposite.op (τ e) *
          (word.map (fun f => MulOpposite.op (τ f))).prod)
      rw [MulOpposite.unop_mul, MulOpposite.unop_op, ih]
      rfl

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.ChainValuation

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

noncomputable def atomWord (a : Atom S old) : List E :=
  RecursiveRecord.ChainValuation.chosenWord (old a.1) a.2

noncomputable def traversalWord (atoms : List (Atom S old)) : List E :=
  (atoms.map (atomWord S old)).flatten

theorem traversalWord_letters (atoms : List (Atom S old)) :
    ∀ e ∈ traversalWord S old atoms, e ∈ S := by
  intro e he
  obtain ⟨word, hword, heword⟩ := List.mem_flatten.mp he
  obtain ⟨a, _, ha⟩ := List.mem_map.mp hword
  subst word
  exact a.1.property.1
    (RecursiveRecord.ChainValuation.chosenWord_letters (old a.1) a.2 e heword)

/-- Any generator-preserving inclusions evaluate the traversal as the
ordered product of the original block displacements. -/
theorem traversalWord_value {G : Type u} [Group G]
    (edge : E → G) (incl : ∀ A : Proper S, (old A).Carrier →* G)
    (hincl : ∀ A e, e ∈ A.val → incl A ((old A).edge e) = edge e)
    (atoms : List (Atom S old)) :
    ((traversalWord S old atoms).map edge).prod =
      (atoms.map (fun a => incl a.1 a.2)).prod := by
  have hword : ∀ (A : Proper S) (w : List E),
      (∀ e ∈ w, e ∈ A.val) →
      (w.map edge).prod = incl A ((w.map (old A).edge).prod) := by
    intro A w
    induction w with
    | nil => intro _; exact (incl A).map_one.symm
    | cons e w ih =>
        intro hw
        have he := hw e (List.mem_cons_self)
        have htail : ∀ f ∈ w, f ∈ A.val :=
          fun f hf => hw f (List.mem_cons_of_mem e hf)
        simp only [List.map_cons, List.prod_cons, map_mul]
        rw [hincl A e he, ih htail]
  induction atoms with
  | nil => rfl
  | cons a atoms ih =>
      change (((atomWord S old a ++ traversalWord S old atoms).map edge).prod) = _
      rw [List.map_append, List.prod_append, ih]
      rw [hword a.1 (atomWord S old a)
        (RecursiveRecord.ChainValuation.chosenWord_letters (old a.1) a.2)]
      rw [show ((atomWord S old a).map (old a.1).edge).prod = a.2 from
        RecursiveRecord.ChainValuation.chosenWord_value (old a.1) a.2]
      rfl

theorem atomWord_path (a : Atom S old)
    (C : ChainState E (block S old a.1)) :
    MatchingWordPath C.matching (atomWord S old a)
      (C.lastEmbed 1) (C.lastEmbed a.2) := by
  have h := C.last_word_path (block S old a.1) (atomWord S old a)
    (RecursiveRecord.ChainValuation.chosenWord_letters (old a.1) a.2) 1
  change MatchingWordPath C.matching (atomWord S old a)
    (C.lastEmbed 1)
    (C.lastEmbed ((1 : (old a.1).Carrier) *
      ((atomWord S old a).map (old a.1).edge).prod)) at h
  have hv : ((atomWord S old a).map (old a.1).edge).prod = a.2 :=
    RecursiveRecord.ChainValuation.chosenWord_value (old a.1) a.2
  rw [hv, one_mul] at h
  exact h

/-- The first identity is outside the first outgoing attachment.
This condition also asserts that there are at least two blocks. -/
def StartOutsideExit : List (Atom S old) → Prop
  | x :: y :: _ =>
      (1 : (old x.1).Carrier) ∉
        exitSet (block S old x.1) x.2 (left D S old L x.1 y.1)
  | _ => False

/-- A genuine traversal of an already built prefix extends through the
literal finite tail, retaining its separated initial endpoint. -/
theorem buildTail_traversal
    (p c : Atom S old) (R : PairResult D S old L p c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest))
    (pastWord : List E) (point : R.state.Space)
    (hpath : MatchingWordPath R.state.matching pastWord point (R.state.lastEmbed 1))
    (hout : ∀ t, R.state.lastEmbed t ≠ point) :
    let F := buildTail D S old L p c R rest hsep
    ∃ start : F.state.Space,
      MatchingWordPath F.state.matching
        (pastWord ++ traversalWord S old (c :: rest)) start
        (F.state.lastEmbed F.current.2) ∧
      (∀ t, F.state.lastEmbed t ≠ start) := by
  induction rest generalizing p c pastWord with
  | nil =>
      refine ⟨point, ?_, hout⟩
      change MatchingWordPath R.state.matching
        (pastWord ++ traversalWord S old [c]) point (R.state.lastEmbed c.2)
      simpa only [traversalWord, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil] using
        hpath.append R.state.matching (atomWord_path S old c R.state)
  | cons z rest ih =>
      let f := oldEmbed (block S old c.1) (block S old z.1) R.state c.2
        (left D S old L c.1 z.1) (right D S old L c.1 z.1)
        (left_injective D S old L c.1 z.1) (right_injective D S old L c.1 z.1)
      let Rnext := next D S old L R z hsep.1
      have hmap : ∀ e x y, (R.state.matching e).Rel x y →
          (Rnext.state.matching e).Rel (f x) (f y) := by
        intro e x y hxy
        exact Or.inl ⟨x, y, hxy, rfl, rfl⟩
      have hglue : f (R.state.lastEmbed c.2) = Rnext.state.lastEmbed 1 := by
        apply (oldEmbed_eq_newEmbed_iff (block S old c.1) (block S old z.1)
          R.state c.2 (left D S old L c.1 z.1) (right D S old L c.1 z.1)
          (left_injective D S old L c.1 z.1)
          (right_injective D S old L c.1 z.1) _ _).mpr
        refine ⟨1, ?_, (right D S old L c.1 z.1).map_one⟩
        change R.state.lastEmbed (c.2 * left D S old L c.1 z.1 1) = _
        rw [map_one, mul_one]
      have hnextpath : MatchingWordPath Rnext.state.matching
          (pastWord ++ atomWord S old c) (f point) (Rnext.state.lastEmbed 1) := by
        rw [← hglue]
        exact (hpath.append R.state.matching (atomWord_path S old c R.state)).map
          R.state.matching Rnext.state.matching f hmap
      have hnextout : ∀ t, Rnext.state.lastEmbed t ≠ f point :=
        outside_last_propagates (block S old c.1) (block S old z.1) R.state c.2
          (left D S old L c.1 z.1) (right D S old L c.1 z.1)
          (left_injective D S old L c.1 z.1)
          (right_injective D S old L c.1 z.1) point hout
      have h := ih c z Rnext hsep.2 (pastWord ++ atomWord S old c)
        (f point) hnextpath hnextout
      simpa only [buildTail, traversalWord, List.map_cons, List.flatten_cons,
        List.append_assoc] using h

/-- The complete traversal moves a point in the actual original chain.
No action on an independently selected chain model is assumed. -/
theorem buildNonempty_traversal_moves
    (atoms : List (Atom S old)) (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms)
    (hstart : StartOutsideExit D S old L atoms) :
    let F := buildNonempty D S old L atoms hne hsep
    ∃ start : F.state.Space,
      RecursiveRecord.ChainValuation.testWordPerm
        (fun e => (F.state.matching e).perm) (traversalWord S old atoms) start ≠ start := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => exact False.elim hstart
      | cons y rest =>
          let C : ChainState E (block S old x.1) := (initial D S old L x).state
          let R := pair D S old L x y
          let f := oldEmbed (block S old x.1) (block S old y.1) C x.2
            (left D S old L x.1 y.1) (right D S old L x.1 y.1)
            (left_injective D S old L x.1 y.1)
            (right_injective D S old L x.1 y.1)
          let start := f (C.lastEmbed 1)
          have hmap : ∀ e a b, (C.matching e).Rel a b →
              (R.state.matching e).Rel (f a) (f b) := by
            intro e a b hab
            exact Or.inl ⟨a, b, hab, rfl, rfl⟩
          have hglue : f (C.lastEmbed x.2) = R.state.lastEmbed 1 := by
            apply (oldEmbed_eq_newEmbed_iff (block S old x.1) (block S old y.1)
              C x.2 (left D S old L x.1 y.1) (right D S old L x.1 y.1)
              (left_injective D S old L x.1 y.1)
              (right_injective D S old L x.1 y.1) _ _).mpr
            refine ⟨1, ?_, (right D S old L x.1 y.1).map_one⟩
            change C.lastEmbed (x.2 * left D S old L x.1 y.1 1) = _
            rw [map_one, mul_one]
          have hpath : MatchingWordPath R.state.matching (atomWord S old x)
              start (R.state.lastEmbed 1) := by
            rw [← hglue]
            exact (atomWord_path S old x C).map C.matching R.state.matching f hmap
          have hout : ∀ t, R.state.lastEmbed t ≠ start := by
            intro t
            exact (outside_exit_not_new (block S old x.1) (block S old y.1)
              C x.2 (left D S old L x.1 y.1) (right D S old L x.1 y.1)
              (left_injective D S old L x.1 y.1)
              (right_injective D S old L x.1 y.1) 1 hstart t).symm
          obtain ⟨point, hp, ho⟩ := buildTail_traversal D S old L x y R rest hsep
            (atomWord S old x) start hpath hout
          refine ⟨point, ?_⟩
          have hcompleted := hp.completed _
          have hnepoint := ho (buildTail D S old L x y R rest hsep).current.2
          exact fun hfixed => hnepoint (hcompleted.symm.trans hfixed)

/-- The endpoint belongs to the actual finite test recorded by
`testPackage`, with its complete letter permutations. -/
theorem chainPerm_traversal_moves (N : Nat)
    (c : SeparatedChains D N S old L)
    (hstart : StartOutsideExit D S old L (List.ofFn c.val.2)) :
    ∃ point : chainSpace D N S old L c,
      RecursiveRecord.ChainValuation.testWordPerm (chainPerm D N S old L c)
        (traversalWord S old (List.ofFn c.val.2)) point ≠ point :=
  buildNonempty_traversal_moves D S old L (List.ofFn c.val.2)
    (rawChain_list_nonempty N S old c.val) c.property hstart

/-- Recording all the actual chain tests makes this traversal word
nontrivial in the actual augmented stage. The moving point is constructed
above; it is not a hypothesis of this theorem. -/
theorem augmented_chain_traversal_not_one (N : Nat)
    (c : SeparatedChains D N S old L)
    (hstart : StartOutsideExit D S old L (List.ofFn c.val.2)) :
    ((traversalWord S old (List.ofFn c.val.2)).map
      (AugmentedStep.data D S old (chainSpace D N S old L)
        (chainPerm D N S old L) (chainPerm_square D N S old L)).edge).prod ≠ 1 := by
  obtain ⟨point, hmoves⟩ := chainPerm_traversal_moves D S old L N c hstart
  intro hword
  apply AugmentedRecord.impossible_identity_cycle_test D
    (Step.sets S) (Step.groups S old) (Step.edges S old) (Step.involutions S old)
    (chainSpace D N S old L) (chainPerm D N S old L)
    (chainPerm_square D N S old L) (S : Set E)
    (traversalWord S old (List.ofFn c.val.2))
    (traversalWord_letters S old (List.ofFn c.val.2)) c point hword
  change MulOpposite.unop
    (((traversalWord S old (List.ofFn c.val.2)).map
      (fun e => MulOpposite.op (chainPerm D N S old L c e))).prod) point ≠ point
  rw [← RecursiveRecord.ChainValuation.testWordPerm_eq_unop_product]
  exact hmoves

/-- In the actual augmented stage, the displacements of a separated
recorded chain with its first point outside the exit cannot have identity
product. These inclusions only need their prescribed generator values;
their injectivity is not a premise of the word argument. -/
theorem augmented_chain_displacement_product_ne_one (N : Nat)
    (incl : ∀ A : Proper S, (old A).Carrier →*
      (AugmentedStep.data D S old (chainSpace D N S old L)
        (chainPerm D N S old L) (chainPerm_square D N S old L)).Carrier)
    (hincl : ∀ A e, e ∈ A.val → incl A ((old A).edge e) =
      (AugmentedStep.data D S old (chainSpace D N S old L)
        (chainPerm D N S old L) (chainPerm_square D N S old L)).edge e)
    (c : SeparatedChains D N S old L)
    (hstart : StartOutsideExit D S old L (List.ofFn c.val.2)) :
    ((List.ofFn c.val.2).map (fun a => incl a.1 a.2)).prod ≠ 1 := by
  rw [← traversalWord_value S old _ incl hincl]
  exact augmented_chain_traversal_not_one D S old L N c hstart

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
