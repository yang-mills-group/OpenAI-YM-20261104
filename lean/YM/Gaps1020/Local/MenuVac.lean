import YM.Gaps1020.Local.Unmarked
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared.Post
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Lotus

open YM.RG01.Survive
-- Include the implicit empty-ticket variant so retaining a nil source still
-- uses the forward Cash and charged Choice Ω. Difference vs A's vacuum
-- filter: no early rejection of CLUSTERS by estimates on head count/travel.
-- Only leaf cut & length, OR order above M. Caption literal integral law
-- exported from B2 applied to this same µ. Core admits **all** post/aux
-- Embrasures (Ports without W-collisions) on one Factor.
open Merge Palette PhysicalNext.Repeat.Daisy
open Push.AbsoluteSums.Mixed Push.AbsoluteSums.Reserves Gas Ursell Captain
open AnalyticBridge VerifiedReset Collection Extra.Iteration Quotes Song Match Geo


open PhysicalNext.Repeat.Lotus
-- anchor is actual alliance. Supports and output rays can be transported to that same J with fees.
variable {R':RG.Rep G f}{J:Cash W s μ L Q o C T R'} (v':Match.Alliance J H 1 0)

def pathSide (J:Cash W s μ L Q o C T R')(R:RG.Rep G f)(γ:ℝ) (i:Magazine J): Config G c→ℝ:= Sum.elim (fun _=>0) (sounding T.down T.low R.beta γ) i
-- keep exact, including path tally (post kinetic approach via tally & this covariance).
def select (F: H.fragrances→ Config G c→ℝ) : Magazine J→ Config G c→ℝ := Sum.elim (fun i=> (-1:ℝ) • F (v'.furrow i)) (fun _=>0)
def jointE (t:ℕ→Prop) (M:ℕ)(χ:Chi):= Post.select v' (fun i=> seatZ i M χ t)
def couponSet (t:ℕ→Prop) (M:ℕ)(χ:Chi):= choir (jointE v' t M χ) ∘ pennant J
def retainedE (M:ℕ)(χ:Chi) (γ:ℝ): Magazine J→ Config G c→ℝ:= pathSide J R γ + jointE v' (fun t=> ¬M+1≤ t) M χ
def lowCurve (M:ℕ)(χ:Chi) (γ:ℝ):= choir (retainedE v' M χ γ) ∘ pennant J
local notation "Tᴹ" => (fun p:ℕ=>M+1≤ p)
lemma piecesAll (χ) (γ:ℝ) (i:Magazine J): opus J v' χ γ i= retainedE v' M χ γ i+jointE v' Tᴹ M χ i:=by
   rcases i with i|i; swap; · unfold retainedE jointE pathSide Post.select opus; simp
   unfold retainedE jointE pathSide Post.select opus Song.sequence; simp only [Pi.add_apply,Sum.elim_inl,zero_add]; rw [s_revenue,z_split _ _ Tᴹ,smul_add]; abel
lemma composeCurve (χ) (γ:ℝ) : (plusone J v' χ γ).logRead=lowCurve v' M χ γ+couponSet v' Tᴹ M χ:=by unfold lowCurve couponSet; rw [YM.GapsLocal.Vacuum.sung]; change choir (opus _ _ _ _) ∘ _ = _; rw [show opus J v' χ γ= _ from funext (piecesAll (M:=M) v' χ γ)]; rfl
variable (D:BudgetPoint) (t:ℕ→Prop)
-- Beam ***site different*** from locate J. Decorative apportionment has to pay, no congr site assertion.
lemma scheduleAt {Y':RG.Stage} (N: Captain H Y'.order C' d v Y A b r B q k χ)(Γ:Target.Expense Q)(Z':Magazine J→Prop)
    (h:MixReceipt (D:=Y') Γ M N) (hs:D.B=radiusB s)(ht:D.threshold=Pressure.temp s)(hj:D.order≤Y'.order)(hy:D.power=Y'.power)(hf:preExponent D ≤ Γ.earn)
    (i:ℕ)(he:∀ n,t n→ i≤ n):
    let f (j:Magazine J):= if Z' j then jointE v' t M χ j else 0
    Meadow.Budget D (Beam.marquee J D).reg (choir f ∘ pennant J) (turnFee D*((horizonRadius G L s^i)⁻¹)):=by
   intro f; let R0 := horizonRadius G L s
   have hx:= hostPaid t M Γ D N ht hs hj hy h i _ hf he
   let g : Magazine J→ℝ:= Sum.elim (fun j=> zPrice N (v'.furrow j) M D R0 t) (fun _=> 0)
   have hv (p:Magazine J):0 ≤ g p:=by rcases p with i|i; exact zp_nonneg N (v'.furrow i) D t (zero_le_two.trans h.large); rfl
   let F:= Beam.contents J D
   have hH(i:J.fragrances): (Beam.contents J D (.inl i)).support=reachability (v'.furrow i):= (Beam.see J i).trans (reconnects J v' i)
   have hE := Meadow.soared (I:=J) D f (t:= (R0^i)⁻¹)
   refine hE ⟨g, ?_, fun k=>?_⟩
   · intro m; rw [← add_zero ((R0^i)⁻¹)]
     have ht:= Cost.equiv v'.furrow (hx.1 m); apply Cost.sum
     · refine budget_mono ht (fun i=>?_) (fun i=>?_)
       · split; next h=> exact mul_nonneg (hv (.inl _)) (Real.exp_pos _).le
         next h=> exact le_rfl
       split; next h=>
         change g (.inl i) * Real.exp (preExponent D* ↑(coverNumber D.B _)) ≤ if m∈reachability (v'.furrow i) then _ else 0
         rw [if_pos (show m∈ reachability (v'.furrow i) from (hH i) ▸ (h ▸ (Beam.contents J D (.inl i)).anchor)),hH]; rfl
       next h=> exact ht.1 _
     simp [SumBudget,g]
   unfold f; split
   next h=>
     rcases k with k|k
     · have ht := hx.2 (v'.furrow k) (F (.inl k)).site (show _ from (hH k) ▸ (F (.inl k)).anchor)
       rw [hH]; exact ⟨CouplingShape.reg_scale _ ht.1,by simpa only [abs_neg,abs_one,one_mul] using! CouplingShape.sup_scale (-1) ht.2⟩
     exact ⟨CouplingShape.reg_const _, VerifiedReset.sup_le (CouplingShape.sup_const (o:=_ ) 0) (le_of_eq abs_zero)⟩
   next h'=> exact ⟨CouplingShape.reg_const _,VerifiedReset.sup_le (CouplingShape.sup_const (o:=_) 0) (abs_zero.trans_le (hv k))⟩
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared.Post
