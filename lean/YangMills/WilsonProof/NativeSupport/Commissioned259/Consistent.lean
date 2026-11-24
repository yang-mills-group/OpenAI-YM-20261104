import YangMills.WilsonProof.NativeSupport.Commissioned259.Faces

/-! # Even the *chosen* formal Far coefficients are coherent under unit padding

One can simply use the theorem of `Matched` on every proper subarray; no need for an identity
about the different purchases. Here we prove the stronger statement that the array purchases in
this normalization **do** agree with those on padding and, when doing an empty Near by exact unit,
even the formal through-h projection gives that unit. Proof: use F.O (generalize just by linearity
in the Near fields) and the exact `uniqueK` theorem of the prescription (`O/Bind`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set PowerSeries MeasureTheory Maxwell
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land MS.Theater
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Rose
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe O.Bind
variable {G : Gauge} {V : Arenas G} {B : ℝ→Frames G} {R : ℝ→PowerSeries ℂ} {n m p a z : ℕ}
    {d : Fin n→ℕ} {K:Set (Points n)} {S:Set (Points m)}
    (X : O.Canon.Physical V R B)

/-- Unmarked gap at mixed Near caps and alphabet exterior (any common ambient). -/
private abbrev listen {k : ℕ} (V : Arenas G) (v : Scan G m)
    (hd : ∀ i, d i≤k) (hv : totalG v ≤ k) (u : Slots G d) (x : Points n) (y : Points m) :=
  PowerSeries.mk fun p => bareRow V hd (e:=fun _=> totalG v) (fun _ => hv) x y p u
    (inputs (d:=fun _=>totalG v) v (guardT v))

include X in
private lemma mixedGap (u : Slots G d) (x : Points n) (hx : x ∈ conf n) (v : Scan G m) (hd : ∀ i, d i ≤ a) (hv : totalG v ≤ a)
    (hS : IsCompact S) (hy : S ⊆ Outside m) (k p : ℕ) :
    ChargeP p ((k:ℝ)+1+(totalG v:ℝ)) (fun (i:↥S) t =>
      listen V v hd hv u x (squeeze (-t) i.val) - Lamp (install V) k (squeeze (-t) i.val) v (farCf V u x)) := by
  have hi (y:Points m): listen V v hd hv u x y = ∑ b : BasisSlots G d,
      C (coordinates b u) * party (install V) x y (names b) v := by
    ext1 p'
    simp_rw [listen,coeff_mk,map_sum,coeff_C_mul,
      ← bareEntry X.dimensions hd (e:=fun _=>totalG v) (fun _ => hv) x y (included _)
        (d:=d) (hv:=show budgeted v (fun _=>totalG v) from guardT v)]
    nth_rw 1 [word_sigma u (bareRow V hd _ x y p'),_root_.sum_apply]
    rfl
  have hlo (y:Points m) : listen V v hd hv u x y - Lamp (install V) k y v (farCf V u x) =
      ∑ b : BasisSlots G d, C (coordinates b u) * Basket (install V) (names b) v (FarCoefficients V (names b) x) k x y := by
    rw [hi]; simp_rw [Basket,mul_sub,← O.Read.Fare, farCf,Finset.sum_mul,Finset.mul_sum,← mul_assoc]; rw [Finset.sum_sub_distrib,Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)]
  simp_rw [hlo]
  exact ChargeP.sum _ fun b _=> ChargeP.times (ChargeP.fixed _) ((FO X (names b) v (K:={x})
    isCompact_singleton (singleton_subset_iff.mpr hx) hS hy p k).pull fun i => ((⟨x,mem_singleton _⟩ : ↥({x}:Set (Points n))), i))

/-- `uniqueK` on the project's album detects coefficient equality even from homogeneous *zero*
payments (Lamp f ≈ Lamp g). Useful where a coordinate consistency question involves two
different number/layouts of Near inputs. -/
private def agree (V:Arenas G) (k p:ℕ) (f g:Q G→PowerSeries ℂ) : Prop :=
  ∀ m (w : Scan G m) S, IsCompact S → S ⊆ Outside m →
    ChargeP p ((k:ℝ)+1+totalG w) (fun (i:↥S) t => Lamp (install V) k (squeeze (-t) i.val) w f -
      Lamp (install V) k (squeeze (-t) i.val) w g)

include X in
private lemma certified (k p:ℕ) {f g : Q G→PowerSeries ℂ} (H : agree V k p f g) (q : Q G) (hq : heft q ≤ k) (i : ℕ) (hi : i<p):
    coeff i (f q) = coeff i (g q) := by
  let X₀ : Scan G 0 := fun i => Fin.elim0 i
  let c := FarCoefficients V X₀
  let c' (x:Points 0) (q:Q G) := c x q + f q - g q
  let D := ({(0:Points 0)}:Set (Points 0)); have hD : D ⊆ conf 0 := fun _ _ => injective_of_subsingleton _
  have hc := (X.far X₀).2.2 D isCompact_singleton hD k p
  have hl {m:ℕ} (u:Scan G m) (x:Points 0) (y:Points m) : Basket (install V) X₀ u (c' x) k x y =
      Basket (install V) X₀ u (c x) k x y -
        (Lamp (install V) k y u f - Lamp (install V) k y u g) := by
    simp only [c', Basket,Lamp,Settle,add_mul,sub_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib]; abel
  have hc' : Fiasco (install V) D k 1 p X₀ c' := by
    intro m S v hS hv; unfold RangeP; simp_rw [hl]; exact ChargeP.sub (hc m S v hS hv) ((H m v S hS hv).pull Prod.snd)
  have hp' (c : Fable G 0): PlainF D c k p:= by
    intro b _ i _; refine ⟨‖coeff i (c 0 b)‖,fun x =>?_⟩; dsimp only; rw [Subsingleton.elim x.val (0:Points 0)]
  have hz := uniqueK X.scope X.dimensions X.wardRank X.awake zero_lt_one le_rfl hc hc' (hp' c) (hp' c') _ (Set.mem_singleton _) q hq i hi
  change coeff i (c 0 q)= coeff i (c 0 q + f q - g q) at hz
  rw [map_sub,map_add,eq_sub_iff_add_eq,add_right_inj] at hz
  exact hz.symm

section
variable (N : WilsonPrescription G) {sim : G.Simple} (ν : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "Ω" => Scale.Measure.outlook N.scheme N.criterion
local notation "F" => farCf Ω
variable (x : Points n) (hx : x ∈ conf n) (f : Fin p ↪ Fin n) (d : Fin n→ℕ)
include H ν hx

lemma same_coefficients (u : Slots G d) (hu : padLeaf f u) :
    F u x = F (faceSlots f u) (restrictPt f x) := by
  funext q
  ext1 i
  refine certified (H.separatedOPE ν).wilson (heft q) (i+1) ?_ q le_rfl i (Nat.lt_succ_self _)
  intro m v S hS hy
  let c := Finset.univ.sup d + totalG v
  have hd : ∀ i, d i ≤ c := fun i=> le_trans (Finset.le_sup (Finset.mem_univ i)) (Nat.le_add_right ..)
  have hv : totalG v ≤ c := Nat.le_add_left ..
  let l := listen Ω v hd hv u x
  let r := listen Ω v (fun i => hd (f i)) hv (faceSlots f u) (restrictPt f x)
  have he : ∀ᶠ t : ℝ in atTop, ∀ y∈S, l (squeeze (-t) y)=r (squeeze (-t) y) := by
    filter_upwards [O.Read.for_far (K:={x}) isCompact_singleton (singleton_subset_iff.mpr hx) hS hy] with t hw y hy'
    ext1 k
    unfold l r listen; rw [coeff_mk,coeff_mk]
    exact honor N ν M H f (Embedding.refl _) hd _ x (squeeze (-t) y) (hw x (Set.mem_singleton _) y hy') u _ hu
      (fun i hi=> False.elim (hi ⟨i,rfl⟩)) k
  have ht := (mixedGap (H.separatedOPE ν).wilson (faceSlots f u) _ (restrict_conf f hx) v (fun i => hd (f i)) hv hS hy (heft q) (i+1)).sub
    (mixedGap (H.separatedOPE ν).wilson u x hx v hd hv hS hy (heft q) (i+1))
  intro k hk; refine Rain.raise (ht k hk) ?_; filter_upwards [he] with t h i
  refine le_of_eq (congr_arg (fun p:PowerSeries ℂ => ‖coeff k p‖) ?_)
  specialize h i.val i.property
  unfold l r at h
  rw [h]; have hz (A B C : PowerSeries ℂ) : A-B=C-B-(C-A) := by abel
  exact hz .. 
lemma purchased_face (k q : ℕ) (u : Slots G d) (hu : padLeaf f u) (t : ℝ) :
    purchased Ω u x k q t = purchased Ω (faceSlots f u) (restrictPt f x) k q t := by
  simp_rw [purchased,same_coefficients N ν M H x hx f d u hu]

omit hx
private def target (G:Gauge) (k:ℕ) (q:Q G) : PowerSeries ℂ :=
  if h: heft q ≤ k then C (coord (low q h) (leaf G k)) else 0
include hx
private lemma empty_cf (ha : n=0) (k : ℕ) (q : Q G) (hq : heft q ≤ k) :
    farCf (d:=d) Ω (fun i=>leaf G (d i)) x q = target G k q := by
  subst n
  let u : Slots G d := fun i=>leaf G (d i); let a:= F u x
  ext1 i
  refine certified (H.separatedOPE ν).wilson k (i+1) (f := a) ?_ q hq i (Nat.lt_succ_self _)
  intro m v S hS hy
  let e (i : Fin m) := totalG v
  let b : Slots G e := inputs v (d:=e) (guardT v)
  let c := k + totalG v
  have hd (i : Fin 0) : d i ≤ c := Fin.elim0 i
  have he : totalG v ≤ c := Nat.le_add_left ..
  let g:= listen Ω v hd he u x
  have hm : ChargeP (i+1) ((k:ℝ)+1+totalG v)
      (fun (i:↥S) t => Lamp (install Ω) k (squeeze (-t) i.val) v a - g (squeeze (-t) i.val)) := by
    have he := mixedGap (H.separatedOPE ν).wilson u x hx v hd he hS hy k (i+1)
    intro j hj; refine Rain.raise (he j hj) (Eventually.of_forall (fun t i=>?_))
    refine le_of_eq ?_
    dsimp only
    rw [map_sub,map_sub,norm_sub_rev]
  have hEq (y: Points m) (hy: y∈Outside m) : Lamp (install Ω) k y v (target G k) = g y := by
    let E j := bareRow Ω (d:=fun _=>k) (H:=c) (e:=e) (fun (_ : Fin 1)=>Nat.le_add_right ..) (fun _=>he) (0:Points 1) y j
    have hj (j) (w : Toon G k) : coeff j (lonelyG (install Ω) y (flash w) v) = E j (fun _=>theory w) b := by
      symm; exact bareEntry (H.separatedOPE ν).wilson.dimensions (d:=fun _=>k) (u:=Single (flash w)) (e:=e) (H:=c) (fun _=>Nat.le_add_right ..) (fun _=>he) (0:Points 1) y (fun _=>size_le w) (guardT v) j
    ext1 j
    rw [← O.Read.Fare]; have hvis(w:Toon G k): heft (flash w) ≤ k := size_le w
    simp_rw [map_sum,target, dif_pos (hvis _), coeff_C_mul,hj]
    have hc (j:ℕ): (E j) (fun _=>leaf G k) b = coeff j (g y) := by
      let f : Fin 0 ↪ Fin 1 := Function.Embedding.ofIsEmpty
      unfold g listen; rw [coeff_mk]; unfold E
      rw [honor N ν M H f (Embedding.refl _) (d:=fun _ => k) _ _ _ _ hy (fun _ => leaf G k) b (fun _ _=> rfl) (fun i hi=> False.elim (hi ⟨i,rfl⟩)) j, bareRow_apply,bareRow_apply, Subsingleton.elim x (restrictPt f 0)]
      congr! -- ambient c identical, Near different declared caps but empty
    rw [← hc j]
    let p : Slots G (fun (_:Fin 1)=>k) := fun _=>leaf G k
    rw [word_sigma p (E j), _root_.sum_apply]
    let i : ((_:Fin 1) → Toon G k) ≃ Toon G k := Equiv.funUnique ..
    refine Eq.symm (Fintype.sum_equiv i _ _ ?_); intro r
    have same : word (d:=fun _=>k) r = fun _ : Fin 1 => theory (i r) := by
      funext j; fin_cases j; rfl
    change coordinates (d:=fun _=>k) r p * E j (word (d:=fun _=>k) r) b = coord (i r) (leaf G k) * _
    rw [same, coordinates, Fin.prod_univ_one]; rfl
  -- moving S
  intro j hj; refine Rain.raise (hm j hj) (Eventually.of_forall (fun t i=>?_))
  exact le_of_eq (congr_arg (fun w => ‖coeff j (Lamp _ k _ v a - w)‖) (hEq (squeeze (-t) i.val) (lives (-t) (hy i.property))))

omit H ν hx in
lemma crop_C (q : ℕ) (t : ℝ) (b : ℂ) : crop q t (C b) = b := by
  rw [crop_apply, Finset.sum_eq_single 0]
  · simp
  · intro i _ hi; rw [coeff_C,if_neg hi,mul_zero]
  simp

/-- The all-units request (also when n=0). -/
theorem purchased_units (k p : ℕ) (t : ℝ) :
    purchased Ω (d:=d) (fun i => leaf G (d i)) x k p t = leaf G k := by
  let f : Fin 0 ↪ Fin n := Function.Embedding.ofIsEmpty
  rw [purchased_face N ν M H x hx f _ _ _ _ (fun _ _ =>rfl)]
  have eqn (w : Toon G k) : F (faceSlots f (fun i=>leaf G (d i))) (restrictPt f x) (flash w) =
      C (coord w (leaf G k)) := Eq.trans (empty_cf N ν M H _ (restrict_conf f hx) (d ∘ f) rfl k _ (size_le w)) (by unfold target; rw [dif_pos (size_le w)]; rfl)
  simp_rw [purchased,eqn,crop_C]; exact all_sig (leaf G k)
end
end YM.FVA2.GradedFar259
