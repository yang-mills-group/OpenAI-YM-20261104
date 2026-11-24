import YM.LocalLTE.Fan.Fallen
/-! Generation map. Σ origins. Ω value expressions LARGE. Point budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Field
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel Bakers PhysicalNext.Repeat Greenbelt Blaze.Stained Gas Ursell
variable {v z r W w s t y η γ B a μ b C C' q X Y : ℝ} {j n k m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}{χ:Chi}
variable (H:Cash W t μ L Q o a T R)
variable (K:Captain H j C v z r Y C' w B q m χ)
variable {p:ℕ} (D:Slots p→Finset (Veil c f)) (V:Tuple H.ThinP p)
-- unperturbed hard. A prophecy with assembly.
def rune (i:Disk G c)(n:ℕ)(r:ℕ→ℕ)(χ:Chi)(m:ℕ):= ∑ j∈ (Finset.univ:Finset (Gains D n)),if built D j (Fan.levy r) ≥ chip (m+1)-10*slack then lace H D i j χ else 0
 -- arg order edit
section quotes
local notation "ξ"=> (2+Real.exp 1)
variable {u₀:ℝ} (u : Directions G c)(x:Disk G c)(hP:x=(gStep R.beta,u))(hp:flags (Pressure.temp t) (increment (1: Config G c) u)=∅)(hT:Stamp T)
variable (β:ℝ)(hB:1≤ β)(z':ℕ→ℕ)(A:Veil c f→ℝ)
variable (hA:∀ (F: Forest S.ratio)(X:Coat T F),X.x=t→X.width=o.K→∀ k,∀ i∈ D k,
   0≤ A i ∧ A i≤1∧ ∀ b:Air f G,|Fan.vows X R Q o.a x b i| ≤ A i*β^(levy z' i))
variable (hI:∀ k,(D k).card≤ N∧ ∀ (F: Forest S.ratio)(X:Coat T F),X.x=t→X.width=o.K→ (Fan.pool (Field.pin (D k) H) X x).real (cabinet (Field.pin (D k) H) (postponement L t o))ᶜ ≤ u₀)
variable (he:∀ i,(V i).val=arm (D i) ∧ Ac.Spark H.supportP (V i).val ∧ troupe T R Q.halo (radiusB t) (V i).val)
def envelope (β:ℝ)(p:ℝ)(N d:ℕ):=ξ^N*(p+N*(β^mini)^d)

-- reservation lemma uses ONE tableau. [Forest] choose simple
lemma launches (h:∀ j, (D j).card≤ N)(k:ℕ) (hk:1≤k) : (Fintype.card (Gains D k):ℝ) ≤ ((k:ℝ)^N)^(p+1):= by exact_mod_cast charged D h hk
include hp hP hT hA hB H
lemma ample (i:Slots p)(g:LevelsΛ (D i) k) : |perLeaf χ (D i) H g x| ≤ Field.oiled D A i*β^(tones (D i) (levy z') g):= by
    exact bloom (χ:=χ) (D i) H _ _ hP hp hT _ hB z' A (fun F X he h=> hA F X he h i) g
lemma glaze (q:Gains D k) : |lace H D x q χ| ≤ Field.stock D A * β^(built D q (Fan.levy z')):= by
    have he i := ample (χ:=χ) H D u x hP hp hT β hB z' A hA i (q i); unfold lace; rw [abs_prod]; apply (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=> he i)).trans_eq
    rw [prod_mul_distrib]; unfold stock built; rw [Real.rpow_sum_of_pos (zero_lt_one.trans_le hB)]
include V K he hI
lemma lifting (hu:0≤u₀)(k:ℕ)(hk:1≤k) : let J:ℝ:= envelope β u₀ N k; let V₀:=1+J+(k:ℝ)^N
     |(∏ i,leaflet H χ (increment 1 u) (V i))-∑ q:Gains D k, lace H D x q χ| ≤ Field.stock D A *((p+1:ℕ)*J*V₀^(p+1)) :=by
  let R i:= (D i).card
  intro J V₀; have hh':1≤ξ:= by linarith [Real.exp_pos 1]
  have hb0:0≤J:= by unfold J envelope; positivity
  have ht:1≤V₀:=by unfold V₀; linarith only [hb0, show 0 ≤ (k:ℝ)^N by positivity]
  let g i:= leaflet H χ (increment 1 u) (V i); let a i (p:LevelsΛ (D i) k):= perLeaf χ (D i) H p x; let f i:=∑ j,a i j; let A₀:=Field.oiled D A
  let P i:=A₀ i*V₀; obtain ⟨F⟩:= Tree.select S.ratio S.patch.odd_side; let V':=Greenbelt.prism T t χ o.K 1 F
  have hZ i : 0 ≤ A₀ i:= oil_nonneg D (fun i j hj=> hA _ V' rfl rfl i j hj |>.1) _
  have hf i : |f i| ≤ A₀ i * (k:ℝ)^N:= by
    apply (Finset.abs_sum_le_sum_abs ..).trans -- edit
    have hh (v) (hv: v∈ (univ:Finset (LevelsΛ (D i) k))) := (ample (χ:=χ) H D u x hP hp hT β hB z' A hA i v).trans (mul_le_of_le_one_right (hZ i) (Real.rpow_le_one_of_one_le_of_nonpos hB ?_))
    rotate_left
    · unfold tones; exact sum_nonpos fun i hi=> mul_nonpos_of_nonpos_of_nonneg ((financial _ _ _ _).trans (by unfold mini; norm_num)) (Nat.cast_nonneg _)
    apply (sum_le_sum hh).trans
    rw [sum_const,nsmul_eq_mul,mul_comm]; exact mul_le_mul_of_nonneg_left (by rw [Finset.card_univ]; exact_mod_cast rankH D i (hI i).1 hk) (hZ _)
  have h i : |g i-f i| ≤ J*A₀ i := by
    have hJ:= tentacles (D i) H K u x hP hp hT β u₀ hB z' A (fun F X he h=>hA F X he h i) (fun F X=> hI i|>.2 F X) (V i) (he i|>.1) (he i|>.2.1) (he i|>.2.2) k
    refine le_trans hJ ?_; unfold J envelope; change ξ^ (R i)*A₀ i*(u₀+(R i:ℝ)*_)≤_*A₀ i; rw [mul_right_comm (ξ^N)]
    have hx:= (hI i).1; have hv:(R i)≤N:=hx; have hy:=hZ i; gcongr
  have hw i: A₀ i ≤ P i:= le_mul_of_one_le_right (hZ _) ht
  have hx := Bakers.price hb0 univ g f P (fun i _=>(hZ _).trans (hw _)) (by
    intro i _; have h₁:= hf i; have h₂:= h i; refine le_trans (b:=|f i| + |g i-f i|) (norm_le_insert' (g i) (f i)) ((add_le_add h₁ h₂).trans ?_); unfold P V₀; nlinarith only [hZ i])
    (fun i _=> (hf i).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (add_nonneg zero_le_one hb0)) (hZ _))) (fun i _=>(h _).trans (mul_le_mul_of_nonneg_left (hw i) hb0))
  have hz : (∏ i, f i)=∑ q:Gains D k, lace H D x q χ:= by unfold f; rw [Finset.prod_univ_sum,Fintype.piFinset_univ]; rfl
  apply le_trans (b:=↑(univ:Finset (Slots p)).card*J*(∏ i:Slots p,P i))
  · rw [← hz]; exact hx
  unfold P; simp_rw [prod_mul_distrib,prod_const,Slots,A₀,Field.stock,Finset.card_univ,Fintype.card_option,Fintype.card_fin]; exact le_of_eq (by ring)
end quotes
end YM.LocalLTE.Fan.Field
