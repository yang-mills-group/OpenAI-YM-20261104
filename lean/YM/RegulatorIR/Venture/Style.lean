import YM.RegulatorIR.Venture.Mist

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Venture
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
open Calibration
open Epoch VacDay
/-! Gain plus slack and damping on χ. Does not bind projections. -/
open Epoch.League
variable {X I:Type} {M:X→ℕ}{n:Page M→Side} {K:KernelChoices}(S:Circuit M n)(Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G)(s:Page M→Scale){B:Marked M}
variable {p e u r:ℕ} {γ θ:ℝ} {Q : Page M→ℝ≥0∞}
local notation "A₀"=> curtain S Y G
local notation "A₁"=> pathL S Y G
local notation "N₀"=> lnk S G
local notation "T₀"=> S.scroll_j Y G
local notation "K₀"=> valley S Y G Z s
section Repair
local notation "T₁"=> S.payroll Y G Z s
local notation "U₁"=> S.devices Y G Z s
local notation "χ"=> chi S Y G Z s
local notation "ρ"=>predicted S Y G Z s
local notation "N₁"=> drifted S G
local notation "S₁"=> B.age_f
local notation "β"=>B.age_t
section environment
variable {i j:ℕ} (C:Scripted S Y G Z p u B γ)
include C
lemma beam_l : Beam S₁ (N₁ u) (fun i=> (U₁ i).line) :=by refine ⟨_,C.bands.rays,fun i=> Stage.physical _ _ _ _ _ i _⟩
lemma forecast_k : Beam S₁ (N₁ u) (fun i=> (U₁ i).driftL):=⟨_,C.bands.down.add (g:=fun _=>1) (Poly.oneQ _),fun i=> Stage.clockpost _ _ _ _ _ i _⟩
omit C
include Y s Z
lemma epoch_bill {T:Page M→Packet (Foot G) r}(h:VacDay Q β (N₀ u) T): VacDay (Q ∘ Flap.prev) S₁ (N₁ u) (fun i=> offer (first_v S G i) (T i.prev)):=by
 obtain ⟨a,h,h'⟩:=h;refine ⟨_,h.us Flap.prev,fun x=> ?_⟩; let F:=(Step.firstChannel (S.opened G x.prev) (S.opened G x.next)).native; let D:= (S.dialect Y G Z s)
 exact local_offer F (A:=Tariff.native _ (S.l_p x.next) u) (y:=peak_o G (S.l x.prev) (S.l x.next)) (enters S Y G Z s u (show localQ (D.census.cone u x.prev) _ (a _) from h' x.prev))
lemma epoch_P {T:Page M→Packet (Foot G) r} (h:Workday β (N₀ u) T): Workday S₁ (N₁ u) (fun i=>offer (first_v S G i) (T i.prev)):=plain_r (epoch_bill S Y G Z s (plain h))

include C
lemma task {Z':Flap M→ Packet (KFoot G) r}(h: VacDay (Q ∘ Flap.prev) S₁ (N₁ u) Z'): VacDay (Q ∘ Flap.prev) S₁ (fun i=>N₀ u i.next) (fun i=>(U₁ i).pullI (Z' i)):=by
 obtain ⟨c,h,H⟩:= h.pull_t (forecast_k S Y G Z s C); refine ⟨c,h,fun x=>?_⟩; let V:=U₁ x
 exact local_crop (A:=Tariff.native (S.l x.next) (S.l_p x.next) u) (T:=Packet.draft V.driftL (Z' x)) (lastChannel (S.opened G x.prev) (S.opened G x.next)|>.native) (peak_o G (S.l x.prev) (S.l x.next)) (H x)

omit s
lemma mainL_cost (hp:i ≤ p+2)(hv:j≤p+2) : Workday S₁ (N₁ u) (fun w=> mainL K (S.pactP w) G (Z _) i j):=⟨_,C.leg i j hp hv,fun x=>localK K (S.pactP x) G (Z _) _ _ _ (S.width_s x) (S.l_p _)|>.1⟩
lemma mainR_cost (hp:i≤p+2)(hv:j≤p+2) : Workday S₁ (N₁ u) (fun w=>mainR K (S.pactP w) G (Z _) i j):=⟨_,C.arm i j hp hv,fun x=>localK K (S.pactP x) G (Z _) _ _ _ (S.width_s x) (S.l_p _)|>.2⟩
include s
lemma mantle (hp:e≤p)(hv:r≤p+2) (h:∀ i<e,Poly β (fun x=> ‖biases (s x) i‖ₑ)): Workday S₁ (N₁ u) (auxiliary S G Z s e r):=by
 apply Workday.add (mainL_cost S Y G Z C (show e≤p+2 by omega) hv); apply Workday.sum; intro k hk; obtain ⟨hh,hK⟩:=mem_erase.mp hk; have hh':=mem_antidiagonal.mp hK; apply (mainR_cost S Y G Z C (show k.2+2≤p+2 by omega) hv).smul; refine Poly.us (L:=β) (h k.1 ?_) Flap.prev; by_contra! hx; apply hh; exact Prod.ext (by change k.1=e;omega) (by change k.2=0;omega)
lemma led (hp:e≤p)(ht:2≤r) (h:∀ i<e,Poly β (fun x=>‖biases (s x) i‖ₑ)) (i j)(hv:Earlier e r i j): Workday S₁ (N₁ u) (fun p=>(U₁ p).addon i j):=by
 have hx:i≤e:=by unfold Earlier at hv;omega
 by_cases hr:j≤p+2
 · by_cases hy:0 < i
   · simp_rw [fun k:Flap M=>coast_add S Y G Z s hy j k]; refine Workday.add (mantle S Y G Z s C (hx.trans hp) hr (fun _ h'=>h _ (h'.trans_le hx))) ?_; cases show (_<e∨ i=e ∧ r<j) from hv with
     | inl H=> exact Workday.smul (mainR_cost S Y G Z C (show 2 ≤ p+2 by omega) hr) _ ((h _ H).us Flap.prev)
     | inr H=> -- j>2
       simp_rw [fun k:Flap M=>paints S Y G Z k]; simp_rw [peak_dark _ (show j≠2 from by omega), smul_zero]; exact Workday.zeroQ
   have hL:i=0:=by omega
   subst i;simp_rw [fun f:Flap M=> vacuum_lo (U₁ f).addon (Halo.essential (S.lane Y G Z s) f)]; exact Workday.zeroQ
 have he (f:Flap M) :(U₁ f).addon i j=0:=Classical.not_not.mp (fun h'=> hr (le_trans (Halo.essential (S.lane Y G Z s) f i j h').2 (by omega)))
 simp_rw [he]; exact Workday.zeroQ
lemma joints (hp:e ≤ p)(ht:2≤r) (H:∀ i j,Earlier e r i j→ Workday β (N₀ u) fun w=>(T₁).bulk w i j)(h: ∀ i<e, Poly β (fun x=>‖biases (s x) i‖ₑ))(i j:ℕ)(hv:Earlier e r i j) : Workday S₁ (N₁ u) (fun w=>(U₁ w).jVac ((T₁).bulk w.prev) i j):=Workday.add (epoch_P S Y G Z s (H i j hv)) (led S Y G Z s C hp ht h i j hv)
lemma fare_z (hp:e≤p)(ht:2≤r)(hr:r ≤ e+2)(H:∀ i j, Earlier e r i j→ Workday β (N₀ u) (fun w=>(T₁).bulk w i j))(h:∀ i<e, Poly β (fun x=>‖biases (s x) i‖ₑ)): Workday S₁ (N₁ u) (rest S Y G Z s e r) := Workday.add (mantle S Y G Z s C hp (by omega) h) (restoration (beam_l _ _ _ _ _ C) (fun x=>joint_h S Y G Z s x) (joints S Y G Z s C hp ht H h))
end environment
end Repair
end YM.RegulatorIR.Venture
