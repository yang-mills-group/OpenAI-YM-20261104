import YM.RegulatorIR.Skein.Gauge

/-! # Actual W1 response repair at chosen gauge.
Support at leading comes from kinetic demand. Next costs. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Skein
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Train Pupil Momentum Cluster
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{X Y Z I:Type} {P:ℝ} {c f:Side}{e r b i j k p:ℕ}
section
variable {A:Deck P (Foot G) (Book G f)}{B:Deck P (Foot G) (Book G c)}(D:GridStep A B)(J:Layer (Foot G) (Foot G))(V:Gain.Bride G)
variable (T:Orders (Foot G))
local notation "R"=> grain D J V
lemma upwardL {A:Layer X Y}(h:Billed (swap A)) : Billed (leggy A):=by
 obtain ⟨c,hc,H⟩:=h; refine ⟨c,hc,?_⟩;intro x; cases x
 next x=> have he: leggy A (Sum.inl x)=0:=funext (fun i=>by cases i <;> rfl); rw [he,quota_zero];exact bot_le
 next x=>
    unfold quota; rw [← (show Injective (Sum.inl (α:=X) (β:=Y)) from Sum.inl_injective).tsum_eq (?_)]
    exact H x
    rintro (z|z) hz
    · exact ⟨z,rfl⟩
    exfalso; apply hz; change ‖(0:ℝ)‖ₑ*_=0;simp
lemma draft_draw (z:Tuple (Foot G) r){T:Packet (Foot G) r}(K:Layer (Foot G⊕ Foot G) (Foot G⊕Foot G))(J:Layer (Foot G) (Foot G))(he:∀ i j,K (Sum.inr j) (Sum.inl i)=J i j)(ht:Limits T)(h:Billed K): drawing (offer (firstChannel A B).native T) K (List.finRange r) (acrossT (lastChannel A B).native z)=unfoldQ (fun _=>J) T z:=by
 rw [wind_up (offerL ht _) K h _ _ (List.nodup_finRange r)]; simp only [Gradient.field,List.toFinset_finRange]; have hv (t)(z) : Gradient.covers (X:=(Foot G⊕Foot G)) t z (List.finRange r):=fun i hi=>(hi (List.mem_finRange ..)).elim
 simp_rw [if_pos (hv _ _)]
 let f:=(firstChannel A B).native; let p:=(lastChannel A B).native
 rw [← (injectT f).tsum_eq]; apply tsum_congr;intro t;rw [offer_eq];apply congr_arg;exact Finset.prod_congr rfl (fun i _=> he (t i) (z i))
 intro x hx; by_contra! h; apply hx; change offer _ _ _ * _ = 0; rw [offer_zero _ h,zero_mul]
lemma uniform_roll (J:Layer (Foot G) (Foot G))(T:Packet (Foot G) r)(h:IsSym T): IsSym (unfoldQ (fun _=>J) T):=by
 intro i z;unfold unfoldQ;conv_lhs=> rw [← (Tuple.perm (Foot G) i).tsum_eq];
 apply tsum_congr;intro x;rw [show T (Tuple.perm (Foot G) i x)=T x from h i x];apply congr_arg; exact Equiv.prod_comp i (fun j=>J (x j) (z j))
lemma straight_roll (T:Packet (Foot G) r) (H:IsSym T)(h: Limits T)(hh:Billed (swap J)): updateQ ((grain D J V).straight) T 0=unfoldQ (fun _=>J) T:=by
 let v:=(firstChannel A B).native; let q:=(lastChannel A B).native
 rw [show updateQ _ _ _ =_ from draw_update (R).straight T v q (leggy J) (inert_d v q (leggy J)) h (upwardL hh)]; change crop (lastChannel ..|>.native) (symmetry _) = _
 rw [Cluster.crop_clock]; rw [show crop q (drawing _ _ _)= _ from ?_,symmetric_already (unfoldQ (fun _=>J) T) (uniform_roll J T H)] -- q rw
 exact funext (fun x=> draft_draw (A:=A) (B:=B) x (leggy J) J (fun _ _=>rfl) h (upwardL hh))
lemma bobbing (He:D.driftL= Function.swap (Quadratic.hoses (Gain.valve J V))): Gradient.diagonal (firstChannel A B).native (lastChannel A B).native D.driftL ((grain D J V).space) :=by
 intro i q; rw [He]; rw (occs:=.pos [1]) [show q=fun _=>q 0 from funext (fun p=>congr_arg q (Subsingleton.elim ..))]; change loom _ _ _=_
 rw [cardinal]; change J _ (q 0)+ V (i.1.1,i.2) (q 0)-_= J i (q 0)+(_-_); exact add_sub_assoc ..
lemma crossing (V':W1 T e)(Ht:Ranks 2 T)(HH:IsSym (T i j))(Hx:∀ i≤ e,∀ r,Limits (T i r))(hx:Billed (Function.swap J))(h':Billed (Function.swap V))(Hk:Billed D.driftL)(Hp:Acres (halo J V) e)(Ht':D.driftL= Function.swap (Quadratic.hoses (Gain.valve J V)))(he:i ≤ e): D.pullI (offer (firstChannel A B).native (T i j))=unfoldQ (fun _=>J) (T i j)-Gradient.correction ((R).space) T i j:=by
 have hv:= congr_fun (consort D J V hx h' V' Hx Hp Ht he) j
 rw [blankShot _ (show Blank (R).straight from inert_b _ _ _), straight_roll D J V _ HH (Hx _ he _) hx, comprehensive, draw_update (R).space _ _ _ _ (bobbing D J V Ht') (Hx i he j) Hk] at hv -- shape arguments?
 rw [hv]; symm; apply add_sub_cancel_left
end
-- tariff at earlier costs ν local displacement. coefs adaptive, just demand each finite.
section Uniform
variable (Γ:Curve X Y) (ℓ:Tariff Z) (x:X→ Z)(y:Y→ Z) (H:ℕ→ℝ≥0∞)(L:∀ i≤e,Curves Γ ℓ x y i (H i))
variable {F:ℝ≥0∞}(T:Orders X) (U:∀ i<e,∀ r,0<r → localQ (ℓ.uses x) (T i r) F)

def chips (i s:ℕ) (H:ℕ→ℝ≥0∞):= ∑ g∈Gradient.turns i s,∏ k,H (g k)
def taxation (e k:ℕ) (H:ℕ→ℝ≥0∞):= ∑ j∈ Finset.antidiagonal e,∑ i∈Finset.range (k+1),chips i j.2 H
include L U
lemma caretaker : localQ (ℓ.uses y) (Gradient.correction Γ T e i) (F*taxation e i H):=by
 unfold correction; apply local_mono _ (b:= F* (∑ j∈(antidiagonal e).erase (e,0), ∑ b∈Finset.range (i+1),chips b j.2 H)) _ (mul_le_mul_right (Finset.sum_le_sum_of_subset (erase_subset ..)) _)
 simp_rw [mul_sum]; apply local_sum; rintro ⟨a,b⟩ hu; obtain ⟨hc,hm⟩:= mem_erase.mp hu; have he:a+b=e:=mem_antidiagonal.mp hm
 have hb: 0<b:= Nat.pos_iff_ne_zero.mpr fun h=>hc (Prod.ext (show a=e by omega) h)
 apply local_sum;intro r hr; unfold Gradient.drawn; split
 next h=> subst i
          cases r with
          | zero => rw [no_scalar_legs _ Γ (show 0<(a,b).2 from hb)]; exact local_zero _
          | succ r=> unfold updateQ chips;rw [Finset.mul_sum];apply local_sum;intro g hg
                     have ht: Gradient.charge g=b:= (Gradient.turns_iff ..).mp hg
                     rw [cut, dif_pos (Gradient.charge g |> fun _=> show Gradient.charge g = (a,b).2 from ht)]
                     subst b; change localQ _ (symmetry (series Γ g (T a _))) _;apply local_symmetry; exact advice Γ ℓ x y _ g (H∘g) (fun i=>L _ ((Finset.single_le_sum (fun j _=>Nat.zero_le (g j)) (mem_univ i)).trans (by change charge g≤e;omega))) (U a (by omega) _ (by omega))
 exact local_zero _
end Uniform
end YM.RegulatorIR.Skein
