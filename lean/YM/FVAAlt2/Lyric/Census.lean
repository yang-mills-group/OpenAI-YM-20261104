import YM.FVAAlt2.Lyric.Ground
/-! # Full census handshake between Assembly.Fk and Frame heat-recursion using:
 conditioned full HeatCov x, ambient map D, tentative T.U (verify primitive & steps separately).
 Local absolute parser obtains accordingly when contracts charged. Constant retained from previous step explicitly.Herm.Point. Does not drop y=0 harmonics. Mark output arbitrary bit s priced; to access log distribution directly when s atomic. Then Mark.fuse accordingly.Wet payment proofs later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.FVAAlt2.Lyric.CensusT
open Function Finset Filter Set MeasureTheory Matrix Metric
open Marker Multi Order Assembly Laplace Order YM.Extra.Trajectories FormalOPE.RG10 FormalOPE.RG10.Word PowerSeries
open PertExtension PertExtension.Series Radial
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Lyric Lyric RegulatorIR.Diagram RegulatorIR.Diagram.Formal RegulatorIR.Binding Next.SectorChange
open scoped Topology Classical BigOperators ContDiff ENNReal Matrix PowerSeries
variable {I J V:Type}[Fintype I] [DecidableEq I][Fintype J][DecidableEq V] {R:Marker.Census V} 
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (z:E)(F:(I→ℝ)→ₗ[ℝ] E) (l:Multi.Hot R→ ℕ)(U:Multi.Hot R→E→ℂ)(g:E→ℝ)
variable (L:Matrix I I ℝ)(T: RegulatorIR.Diagram.Orders J)(S: RegulatorIR.Diagram.Orders J)(D:Matrix J I ℝ)(v:J→ℝ) (s:R.Mode) (m:ℕ)
variable (hL : L.PosDef)
local notation "κ"=> Capacity.direction D
local notation "μ"=> Next.SectorChange.Gaussian.cloud L
local notation "Q"=> Capacity.origin L hL
local notation "A"=> ((D*L)*Dᵀ) -- defeq Π? use Layer abbreviation
local notation:max "b_" k:max => (v + D*ᵥ k)
local notation "Ω"=> Assembly.translate z F
local notation "Y"=> expo (rated (fun i=> i+2) T)
local notation "Ξ"=> ceaseHeat (A) T true
local notation "Z" => (expo (flavor 2 v (ceaseHeat A T true)))
local notation "S₀"=> endHeat m (A) (logHeat A T true) S
local notation "S'" => flavor m v (S₀)
local notation "W"=> rated (fun i=> i+m) S
local notation "Λ"=> Diagram.burn (Capacity.origin L hL) (Capacity.direction D) volume
local notation "γ"=> hL.isHermitian
local notation "Θ"=> (Matrix.isHermitian_iff_isSymm.mp (γ)) -- wrong isHermitian type?

-- expose contract through r.Decoupled from choices. Outer PHY supplies.
structure RiteV (r:ℕ) : Prop where
  hefty : Vacuum T
  fresh : gradedSymmetric T
  earnings (i:I→ℝ)(e:ℕ)(he:e≤r): Assembly.vacuumLetter g (Ω i) e= coeff e ( flavor 2 (v+D*ᵥ i) T )
variable [Fintype V]
structure MarkV (r:ℕ):Prop where
  known : gradedSymmetric S
  cap e : Within (e+m) (S e)
  gage (i:I→ℝ)(e:ℕ)(he:e≤r) : coeff e (Word.see s (markExp (Assembly.curve l U (Ω i))))=(↑( coeff e ( flavor m (v+D*ᵥ i) S )):ℂ)

variable (r:ℕ)(hv : RiteV z F g T D v r)
local notation "T'"=> Assembly.prescription z F l U g L ( Matrix.isHermitian_iff_isSymm.mp hL.isHermitian ) r
section Ledger
include hv
omit [Fintype V] in
lemma payout (x:I→ℝ)(e:ℕ)(he:e≤r): PertExtension.Series.Radial.expsum (Radial.layers g) e e (Ω x)= MvPolynomial.eval (v+D*ᵥ x) (coeff e Y) := by
    let P:=emphasis b_ x; have hp:= Capacity.painter (q:= flavor 2 (v+D*ᵥ x) T) (y:=Ω x) (v:=PertExtension.Series.Radial.layers g) (fun i hi=> (Assembly.vacuum_eq ..).symm.trans (hv.earnings x i hi)) he ; rw [←hp, flavor, ← map_exp (G:=P), PowerSeries.coeff_map]; exact language _ _
omit hv
lemma squared : Diagram.Gaussian.bond (Q) κ=A := funext fun i=> funext fun j=> Capacity.sensed L hL D i j
include hv
-- denominator never power-scaled because in absolute charter
lemma shelters : Λ Y v= Z:= by
    have hw:= Capacity.unmarked L hL D T v hv.hefty hv.fresh; rw [squared] at hw; exact hw
omit hv in
lemma leadCur (x:E): vac R (Assembly.curve l U x)=0:=by ext1 i; rw [vac_eq,unfold_see, mark_curve_quiet,map_zero]
lemma bare_one (x:E)(e:ℕ) : coeff e (Word.see R.quiet (markExp (Assembly.curve l U x)))=( if e=0 then 1 else 0):=by
    change coeff _ (see _ (Word.expMark _))=_; rw [←vac_eq,Word.vac_exp _ (leadCur l U x),PowerSeries.coeff_one]
lemma gathered (v': I→ℝ)(e:ℕ)(he:e≤r) : Assembly.insideMoment z F l U g R.quiet e v'=(↑(MvPolynomial.eval (v+D*ᵥ v') (coeff e Y)):ℂ):=by
    unfold insideMoment Assembly.rows; rw [ expansions, ← Word.unfold_see, ←vac_eq,map_mul, show vac _ (markExp _)=1 from Word.vac_exp _ (leadCur l U (Ω v')),mul_one, vac_eq,unfold_see, realCoeff,beads,if_pos rfl ]; rw [payout z F g T D v r hv v' e he]
lemma devoted (e:ℕ)(he:e≤r): detail T' R.quiet e= (↑(coeff e Z):ℂ):=by
   unfold detail; rw [Assembly.order_read z F l U g L (Θ) hL R.quiet he, ← shelters z F g L T D v hL r hv,Capacity.harvest]; simp_rw [gathered z F l U g T D v r hv _ e he]; exact integral_ofReal
lemma den : logVac T'=Order.series R r (realCurve R (fun i=> coeff i (flavor 2 v (Ξ)))) := notice (Assembly.prescription_sym _ _ _ _ _ _ _ hL) (flavor_dark _ (vacuum_lo _ (warmed _ T hv.hefty)) _) fun i=> devoted z F l U g L T D v hL r hv i

variable (hs:MarkV z F l U S D v s m r)
include hs
lemma burnt : Λ (Y*W) v= Z*S':=by
    have he:= Capacity.marked L hL D T S v hv.hefty hv.fresh hs.cap hs.known; dsimp only at he; rw [squared, shelters z F g L T D v hL r hv] at he; exact he
set_option maxHeartbeats 200000 in
lemma staged (v': I→ℝ)(e:ℕ)(he:e≤r) : Assembly.insideMoment z F l U g s e v'=(↑(MvPolynomial.eval (v+D*ᵥ v') (coeff e (Y*W))):ℂ):= by
    unfold insideMoment Assembly.rows; rw [ expansions, coeff_mul, Marker.Poly.part_sum, coeff_mul,_root_.map_sum,Complex.ofReal_sum]; apply sum_congr rfl; intro i hi; simp_rw [realCoeff, Marker.Poly.product_bead, Marker.Poly.part_smul, _root_.map_mul, Complex.ofReal_mul]
    have h:= mem_antidiagonal.mp hi; have hh:=hs.gage v' i.2 (by omega); rw [Word.unfold_see, flavor_lo] at hh; rw [payout z F g T D v r hv v' i.1 (by omega), hh,rated_v]
lemma aboard (e:ℕ)(he:e≤r) : detail (Order.ratio T') s e=(↑(coeff e (flavor m v S₀)):ℂ):=by
   refine exposes (Assembly.prescription_sym _ _ _ _ _ _ _ hL) (Assembly.prescription_unit ..) s (u:=Z) (exp_start _) (fun i=> devoted z F l U g L T D v hL r hv i) ?_ e he
   intro i hi; unfold detail; rw [ Assembly.order_read _ _ _ _ _ _ _ hL s hi, ← burnt z F l U g L T S D v s m hL r hv hs, Capacity.harvest]; simp_rw [staged z F l U g T S D v s m r hv hs _ i hi]; exact integral_ofReal
omit hs hv in
lemma welcomed (x:E)(u:V)(e:ℕ) : coeff e (Word.see (R.fire u) (Assembly.markExp (curve l U x)))= Assembly.markLetter l U (⟨ R.fire u, Finset.singleton_nonempty _⟩:Multi.Hot R) x e:= by
   let f:= Assembly.curve l U x; have hv: vac R f=0:= leadCur l U x
   rw [show markExp _=Word.expMark f from rfl, ← Word.alone _ (Word.vac_exp f hv) u, log_exp f hv, Word.unfold_see]; unfold f curve; rw [ PowerSeries.coeff_mk ]; exact part_lit _ ( ⟨ R.fire u, Finset.singleton_nonempty _⟩:Multi.Hot R )
end Ledger
end YM.Comparison.RG02.FVAAlt2.Lyric.CensusT
