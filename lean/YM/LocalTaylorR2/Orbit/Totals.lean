import YM.LocalTaylorR2.Orbit.Chariot
import YM.MergeProof.Garden
/-! Tree leases & ALL marker quantities before second tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ s κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R) (X:Coat T F) (H:Cash W s μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G} (χ:Chi) (p:H.ThinP)
local notation "Θ"=>p.val
local notation "Ω"=> (M.signs S)
open Marker Charge Tender Port
local notation "V"=> Paint (restP M H p)
local notation "T₀"=> restP M H p
local notation "HG"=> H.unionP Θ
local notation "Ψ"=> Orbit.checked M H p ∧ Clear T₀
variable {j l k n:ℕ} {D K e v₀ d r z ξ x b' a' B' R' A c' θ ζ ρ:ℝ}
variable (ht: Tinted G s K d o.a L χ j) (U:StoresR2 H j v₀ d A D k x n χ)
variable (N:Captain H j b' d v₀ w A a' r B' R' (n+j) χ) (Ξ:Utopia H j v₀ d r b' χ)
variable (hB:LocalBookingsR2 ζ c' N.conduit)(h:1≤betaF G s L)(hζ:0≤ζ)(hs:1≤θ)(hp:1≤ρ)(hP:ρ*c'≤1)(hK:ρ^(l+1) ≤ betaF G s L^ζ)(hM:betaF G s L^ζ ≤ Real.exp (Q.mark L μ s))
local notation "Φ"=> N.conduit
local notation "η"=> (l+1:ℝ)*θ*ρ
local notation "γ"=> (1+H.shapeW Θ)^(n+j)
local notation "φ"=> truck D x K r l j
abbrev cars (K D θ ζ x ρ:ℝ) (l:ℕ):=if Orbit.checked M H p then M.weight* (∏ i∈T₀,entry (Φ) ((l+1:ℝ)*θ*ρ) ζ i)*truck D x K r l j*γ else 0
-- !! η notation depends section variable θ ρ l (shadow)! common same names hidden. Lean macro expansion in binder test with #print
include hs hp in
lemma height : 1≤η:= one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg _)) hs) hp
include h hζ hs hp ht U
lemma carsN : 0≤ cars M H χ p N K D θ ζ x ρ l:=by
  unfold cars; split
  · have he:0≤ (∏ i∈ T₀, entry (Φ) (η) ζ i):= prod_nonneg fun i _=> ((Φ).fares i).trans (Tender.cheap (Φ) h hζ (height hs hp) i); unfold truck speedS; have hT:= ht.salt; have hv:= (Φ).active; have hp:= U.sure; have hx':= U.fuel; have h':=H.positive_volume Θ;have hw:= M.profit; positivity
  exact le_rfl
local notation "q₀"=> receipt M H χ p N D x K θ
include hB hP hK hM
lemma totalA : (∑ i:Orders l,q₀ i *ρ^i.val) ≤ cars M H χ p N K D θ ζ x ρ l:=by
  by_cases hc:Orbit.checked M H p; swap; · simp [cars,receipt,hc]
  let t:= T₀; let q:=η; let g:=(1+H.shapeW Θ)^(n+j); let hF:=φ
  have hg:0≤g:= pow_nonneg (add_nonneg zero_le_one (H.positive_volume Θ)) _
  have h': 0≤ hF:= by unfold hF truck speedS; have hT:= ht.salt; have hv:= (Φ).active; have hp:= U.sure; have hx':= U.fuel; positivity
  have hd:1≤q:=height hs hp
  unfold cars receipt; simp_rw [if_pos hc]; by_cases he:Clear (restP M H p); swap
  · simp_rw [if_neg (show ¬ Ψ from by exact fun h=> he h.2)]; rw [sum_eq_single (perch l),if_pos ⟨rfl,hc⟩]; rotate_left; · intro i _ hi; rw [if_neg (fun h=> hi h.1),zero_mul]
    · simp
    set a:= ∏ i∈t, (Φ).fare i with ha; let U₀:=∏ i∈t, entry (Φ) (η) ζ i
    have hr: ρ^(l+1) * a ≤ U₀:= by
      unfold Clear at he; push Not at he; obtain ⟨i,hi,he⟩:=he
      unfold U₀; rw [ha,← mul_prod_erase t _ hi,← mul_prod_erase t _ hi,← mul_assoc]; apply mul_le_mul ?_ (prod_le_prod (fun _ _=> (Φ).fares _) (fun _ _=> Tender.cheap (Φ) h hζ hd _)) (prod_nonneg fun _ _=> (Φ).fares _) ((Φ).fares _|>.trans (cheap _ h hζ hd _)); exact ((mul_le_mul_of_nonneg_right hK ((Φ).fares _))).trans (polluter_cost (Φ) h hd Θ hc.1.2 hM ((Finset.mem_sdiff.mp hi).1) he)
    calc _ = M.weight*(ρ^(l+1)*a)*hF*g:= by change M.weight * _*hF*g*ρ^(l+1)=_; unfold a t hF g; ring
         _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr M.profit) h') hg
  simp_rw [if_pos (show Ψ from ⟨hc,he⟩)]; refine (Candle.money (U:=T₀) (l:=l) _ (fun i=> artNN M H χ p ht U N hs i) hp).trans ?_
  apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Tender.inflated _ hB h hζ hs t (isPure he) hp hP) M.profit) h') hg)
  apply le_of_eq; rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]; exact sum_congr rfl fun q _=> by unfold artA; unfold hF g; ring

variable {ι:Type} [Fintype ι] (Y:ι→Leaf R) (u:ι→ℝ)(hU:YM.Merge.Palette.Plot Y H u)
open YM.Merge Palette
local notation "aY"=> sign Y S
local notation "E"=> Tickets aY
local notation "uY"=> wages Y u
local notation "U₀"=>entry (Φ) (η) ζ
-- aggregate.Cost EVEN casts squarefree; distinct ticket body normative.
abbrev turnWeight (s:Tickets (Palette.sign Y S)) : ℝ:= ∏ i∈ s.val, u i
abbrev edit (ξ ζ:ℝ)(i:Head S):=entry Ξ ξ ζ i + Tickets.extra (Palette.sign Y S) uY i
abbrev footing (ξ ζ:ℝ)(n:ℕ)(p:Molecule S):= if H.ticketsP 0 0 0 p then (∏ i∈p, edit H χ Ξ Y u ξ ζ i)*(1+H.shapeW p)^n else 0
abbrev totalBill (K D θ ζ x ρ:ℝ) (l:ℕ):=truck D x K r l j* footing H χ (Φ) Y u ((l+1:ℝ)*θ*ρ) ζ (n+j) Θ
omit ht U h hs hp hζ hB hP hK hM
include hU
lemma twN (x:E):0≤ turnWeight Y u x:= prod_nonneg fun i _=> hU.live i
lemma wagesN (x:ι): 0≤ wages Y u x:= mul_nonneg (hU.live x) (Y x).profit
lemma feeN (i:Head S)(h:1≤ betaF G s L)(hζ:0≤ζ)(ht:1≤ξ):0≤edit H χ Ξ Y u ξ ζ i:= add_nonneg ((Ξ.fares _).trans (cheap Ξ h hζ ht _)) (sum_nonneg (fun i _=>by split; exact wagesN H Y u hU _; rfl))
include ht U h hζ hs hp
lemma totalN: 0≤ totalBill H χ p N Y u K D θ ζ x ρ l:=by
  apply mul_nonneg
  · unfold truck speedS; have hT:= ht.salt; have hv:= (Φ).active; have hp:= U.sure; have hx:= U.fuel; positivity
  unfold footing; split
  · exact mul_nonneg (prod_nonneg fun i _=>feeN H χ (Φ) Y u hU _ h hζ (height hs hp)) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume Θ)) _)
  exact le_rfl
include hB hP hM hK
lemma turnout : (∑ i:E, ∑ t:Orders l, turnWeight Y u i * receipt (Palette.team Y i) H χ p N D x K θ t *ρ^t.val) ≤ totalBill H χ p N Y u K D θ ζ x ρ l:=by
  apply le_trans (Finset.sum_le_sum (g:=fun i:E=> turnWeight Y u i * cars (Palette.team Y i) H χ p N K D θ ζ x ρ l) (s:=univ) ?_) -- v polynomial
  · by_cases ht': H.ticketsP 0 0 0 Θ
    · unfold totalBill footing edit; rw [if_pos ht', Tickets.expanded,Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      have h₀: 0≤φ:=by unfold truck speedS; have hx:= U.sure; have hy:= U.fuel; have hm:= ht.salt; have hq:= (Φ).active; positivity
      unfold cars; split
      next hi=>
        rw [if_pos (show i.reach⊆Θ from Palette.label Y i ▸ hi.2),restP,Palette.label,Palette.worth]; unfold Palette.wages; rw [Finset.prod_mul_distrib]; apply le_of_eq; unfold turnWeight; ring -- nt lost μ 
      rw [mul_zero]; apply mul_nonneg h₀ (mul_nonneg _ (pow_nonneg (add_nonneg zero_le_one (H.positive_volume Θ)) _)); split
      next hx=> exact mul_nonneg (prod_nonneg fun i _=>wagesN H Y u hU i) (prod_nonneg fun i _=> ((Φ).fares _).trans (cheap _ h hζ (height hs hp) i))
      exact le_rfl
    have hr (i:Team R):¬checked i H p:=fun h=> ht' ((H.attends _).2 h.1.1)
    simp only [totalBill,footing, cars,hr,ht', ite_false,mul_zero,sum_const_zero]; rfl
  intro i _
  simp only [mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (totalA (Palette.team Y i) H χ p ht U N hB h hζ hs hp hP hK hM) (twN H Y u hU i)
end YM.LocalTaylorR2.Orbit
