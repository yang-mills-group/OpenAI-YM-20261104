import YM.FVAAlt2.Boot.Revenue
/-! # Native.Local.Path business. Never assert $World.Ledger$ data follows Local until filling pin-reader $Setup photostream. Given `hire`. `progressesT` etc.

Prove e=0 FeeAct agrees even without higher elementary factors. The only projected-away pieces are scalars at y=0 after reading output. (Tangent occupancy as derived, no Level≥5.Delta) -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Pipeline.See
open Function Set Filter Finset MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Lattice RG Precision Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral Wilson Exterior Arm Marker Multi
open PowerSeries Integration Integration.LocalFormal RunFormalChain PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {m r :ℕ} {G:Gauge} {R X:Type} [DecidableEq R] {Q:KernelChoices} {M:X→ℕ} {N:Page M→Side}
open Oracle Period.Field
variable {C:Circuit M N}
section empty
variable {p:RG.Clip}{U:PathData G}{c:Side}{S: Census R}(F:Colors S G c)(T:UnitCost)
local notation "M'"=> Gala.feeAct p U T F
local notation "X'"=> fieldDir G c 1
local notation "υ"=> (mainTerm p U ∘ (represent (G:=G) (n:=c)))
local notation "τ"=> T.enter
variable {a B Λ:ℝ}(H:U.Bounds p a B Λ)(x:fieldDir G c 1)
include H
lemma on_view (h:Well F): let T' := tale ( Gala.feeAct p U T F x ); (∀ i<2, coeff i T'=0) ∧ coeff 2 T' =Assembly.jet ( mainTerm p U ∘ represent ) 2 x :=by
    -- differentiation: vac+ β, route fees through GradeAt. record primary
    intro T'
    let η(t:ℝ):= (τ t,t • x); have hz: η 0=(0: ℝ × X') := by simp [η]
    have ht:= T.here.prodMk (contDiffAt_id.smul (contDiffAt_const (c:=x)))
    have H₁ := h.suppose_vac.coarse (g:=η) ht hz
    let V(t:ℝ):= t^2*Precision.loop U (sample t x); let Q(t:ℝ):=mainTerm p U (sample t x)
    have hF: Assembly.GradeAt 2 υ:= by
        constructor; exact Extra.Iteration.Calibration.main_jet (n:=c) H
        intro i hi; ext x; interval_cases i
        · rw [iteratedFDeriv_zero_apply]; exact main_origin p U H
        rw [iteratedFDeriv_one_apply,show fderiv ℝ υ 0=0 from main_first p U H];rfl
    have hB: Assembly.GradeAt 2 Q:=hF.coarse (g:=fun t:ℝ=>t • x) (contDiffAt_id.smul contDiffAt_const) (zero_smul ..)
    let p':= Bulk.projected F.vac ∘ η; let L:=Ribbon.fees T
    have hR : Assembly.GradeAt 3 V:=by
       let f(x:X'):=Precision.loop U (represent x); have ht':Assembly.GradeAt 1 f:= Assembly.GradeAt.anchored (loop_smooth (m:=c) p U H) (by unfold f; rw [link_one]; exact loop_origin p U H ); exact (Assembly.GradeAt.shifts (fun t:ℝ=>t) contDiffAt_id rfl 2).mul (ht'.coarse (g:=fun t:ℝ=> t • x) (contDiffAt_id.smul contDiffAt_const) (zero_smul ..))
    have hL : ContDiffAt ℝ ω L 0:= Ribbon.ordered T; let Z' : ℝ→ℝ:= (L-1)*Q+L*p'+V
    have hz1: Assembly.GradeAt 1 (L-1):= Assembly.GradeAt.anchored (hL.sub contDiffAt_const) (by unfold L; change Ribbon.fees T 0-1=0; unfold Ribbon.fees; rw [T.origin]; norm_num); have he: Assembly.GradeAt 3 Z':= ( (hz1.mul hB).add ( Assembly.GradeAt.unchecked hL|>.mul H₁ ) ).add hR
    have hp : Gala.feeAct p U T F x = Q+Z':= by funext t; unfold Gala.feeAct Z'; change _= Q t + ((L t-1)*Q t+L t*(F.vac (T.enter t) (sample t x))+V t); unfold Q L V; ring
    have hv:T'=tale Q+tale Z':=by unfold T'; rw [hp, tale_add (hB.smooth.of_le le_top) (he.smooth.of_le le_top)]
    have hh(i:ℕ)(hi:i≤2): coeff i T'= Assembly.jet Q i 1:= by rw [hv,map_add,tale_jet,tale_jet, ← Assembly.jet_eq,← Assembly.jet_eq,he.jet_z _ (by omega), add_zero]
    constructor
    · intro i hi; rw [hh i hi.le,hB.jet_z _ hi]
    rw [hh 2 le_rfl]; let S:ℝ→L[ℝ]X':=(ContinuousLinearMap.id ..).smulRight x; have ht:Assembly.jet Q 2 1=Assembly.jet υ 2 (S 1):= Assembly.jet_continuous_right S (hF.smooth.of_le le_top) (1:ℝ); exact ht.trans (by rw [show S 1=x from one_smul ℝ x])
lemma actualVisible (h:Well F)(i:ℕ) : visible S p U T F i x = -(↑(coeff (i+2) (Prim.tale (Gala.feeAct p U T F x))):ℂ):=by
    unfold visible
    split
    next h' => subst i; rw [show 0+2=(2:ℕ) from rfl, (on_view F T H x h).2]
    next _=> rfl
end empty
namespace Urban
variable (r)
variable (Y:Oracle.Program Q)(Φ:∀ B:Patch,B.Branches Q G) (K: PhysicalNext.Repeat.Legato.Run G)(P: Period.Field.SeriesT C Q K.family.path)
variable (S: Marker.Census R)(u:R) (A: X→ Boot.Scout (G:=G) m)
variable (L:Page M→ Binding.Scale)
variable (p:ℕ)(k:Flap M)(V:Times (L:=L) r)
local notation "Γ"=> (fromRun K)
local notation "T'"=> k
local notation "X'"=> (P.vol k.next)
local notation "p'"=> P.start C K.family.path k.volW
local notation "Y₀"=> ( P.stepData C K.family.path p k )
local notation "U'"=> (Halo.bios (P.stepData C K.family.path p k) )
local notation:max "T_" x:max=> V.cloth x
variable (F: See.Agenda P S p)[Fintype R]
abbrev buys (x: fieldDir G (K.family.side (P.vol k.next) p) 1): LocalFormal.Datum K.family S := ⟨p',p,P.vol k.next,P.fresh .., U',directive Y₀,See.before P k (F k.prev),x ⟩
-- exactly the public shared interface.
def price : Display (fieldDir G (K.family.side (P.vol k.next) p) 1):= fun i x=> ( buys K P S p k F x ).vacuumAction Γ r i x

def marksF (i:ℕ) (x:fieldDir G (K.family.side (P.vol k.next) p) 1):= ( buys K P S p k F x ).markedLogCoefficient Γ r i (S.fire u)
variable (h: Setup ( Integration.RunFormalChain.fromRun K) P S u A L p r V F)
include h
lemma jetbook (x:fieldDir G (K.family.side (P.vol k.next) p) 1)(i:ℕ)(hi:i≤r): visible S (P.records C K.family.path p k.next).clip (P.records C K.family.path p k.next).path (V.cloth k.next) (F k.next) i x= Adjacent.born (price r K P S p k F) (V.cloth k.prev) 0 r i x- Adjacent.born (price r K P S p k F) (V.cloth k.prev) 0 r i 0 := h.walks k|>.proper i hi x
lemma readings (x:fieldDir G (K.family.side (P.vol k.next) p) 1)(i:ℕ)(hi:i≤r) : prime P S u L p r V F (x:=k.next) x i= Adjacent.born (marksF r K P S u p k F) ( V.cloth k.prev ) 0 r i x:= (h.walks k).mark_w i hi x
omit h
lemma actualRun (x:fieldDir G (K.family.side (P.vol k.next) p) 1)(i:ℕ)(hi:i≤r): marksF r K P S u p k F i x= Integration.LocalFormal.runCoefficients K (buys K P S p k F x) r i (S.fire u):= ( Lyric.logo (Bulk.fk_sym ..) (Bulk.fk_unit ..) u hi).symm
end Urban
end YM.RegulatorIR.FVAAlt2.Pipeline.See
