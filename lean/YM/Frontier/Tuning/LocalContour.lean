import YM.Frontier.Tuning.GaussContour
/-!
# Support-sized contour formula for the actual first component integral.
`stamp` on the real slice includes the conditional F.order integral of free group
variables. No summability of the full gas inferred here; this statement is on one
label at a time. The atlas test gives a way to get the strong holomorphic estimates
later when there is one weighted majorant, since the absolute-value cost before
integrating is now only `markup` with number of needed marginal coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.LocalContour
open Function Filter Set Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Bid
open ConnectedActivityE6 Shell Channel SliceRows Control Window Census Mask Pulse Itinerary Coat
open Packets Presented Sector Raw ProbabilityTheory Poll Pond ComplexVertex GaussContour
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {W x μ C D : ℝ} {L : Side} {R R' : Rep G f} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}

lemma spill_homogeneous {ι:Type}[Fintype ι][DecidableEq ι](b:Finset ι)(t : ℝ)(z : Body (↥b)):
    spill b (t • z)=t • spill b z:=by ext i; by_cases h:i∈b <;> simp [spill,h]
lemma scales_cancel (I : Finset (Tubular f G))(t:ℝ) (z : Body (↥I)) (ht:0<t): heat t (spill I ((Real.sqrt t)⁻¹ • z))=spill I z:=by rw [spill_homogeneous,ComplexVertex.heat,smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr ht).ne',one_smul]

def rawAt (I : Finset (Tubular f G)) (X : Coat T F) (k : Finset ℕ) (s : Molecule S) (R : RG.Rep G f) (v l : Payload G f) (Ñ : ChartRatio G) (z : ℂ) (W a : ℝ) (h : ℕ) (Y:F.Slice G) := evaluate (circuit I X.relating)
     (fun u=> ∏ i∈s, rawCvertex (X.wrapY Y) R v l Ñ z W a k h (spill I u) i) z

def stamp (I : Finset (Tubular f G)) (X : Coat T F) (k : Finset ℕ) (s : Molecule S) (R : RG.Rep G f) (v l : Payload G f) (Ñ : ChartRatio G) (z : ℂ) (W a : ℝ) (h : ℕ):= ∫ Y, rawAt I X k s R v l Ñ z W a h Y ∂F.order G

lemma stamp_real {X : Coat T F}{k:Finset ℕ}{s: Molecule S}{R R':RG.Rep G f}{v l : Payload G f}
   (h: Aligned R (R':=R')) (H : Cash W x μ L Q o C T R') {N:ℕ} (hv : N=Q.halo)
   (hx : X.x=x) (hK : X.width=o.K) (hm: X.manifest) {z:ℝ}(hz : z=R'.beta)
   (he:∀ j y,v j y=(R'.activities.E j y:ℂ))(hk:∀ j y,l j y=(R'.activities.K j y:ℂ)): let I : Finset (Tubular f G):=podium S G (H.unionP s) X.B
    stamp I X k s R v l Q.table z W o.a N = (X.attains R' Q.table W o.a k N s:ℂ):=by
   subst N; intro I
   unfold stamp attains; rw [integral_prod _ (H.integrated X hx hK hm k s),← integral_complex_ofReal]; refine integral_congr_ae (ae_of_all _ fun y=>?_)
   have hp:= (H.laws.data.localP F X hx hK hm).sails.fullC
   have hβ:=hz.symm ▸ H.laws.intake.positive
   rw [rawAt, evaluate_real (circuit I X.relating) (hp.submatrix Subtype.val_injective) _ hβ]
   have hT (t: Body (↥I)) : heat z (spill I ((Real.sqrt z)⁻¹ • t))=spill I t:=scales_cancel I z t hβ
   simp_rw [fun (z') i=>raw_real (X.wrapY y) h v l Q.table W o.a k Q.halo (spill I ((Real.sqrt z)⁻¹ • z')) i he hk hz.symm hβ Q.table_exists.scale,hT, ← Complex.ofReal_prod, integral_complex_ofReal]
   apply congr_arg Complex.ofReal; let f' (w:Air f G) := X.body R' Q.table W o.a k Q.halo s (y,w)
   have hz : confined (swim I) f':=by intro u b hu; apply H.concord s (X.wrapY y) (X.wrapY y) ⟨(Village.refl ..).wrap y y (fun _ _=>rfl),(observe I).mp hu,fun _ _=>Iff.rfl⟩ hx (Finset.Subset.refl _)
   have hA := H.laws.data.access
   have hm': Measurable f':=(show Measurable (X.body R' Q.table W o.a k Q.halo s) from X.body_b Q.table_exists (hx.symm ▸ H.laws.intake) (by rw [hK,hx]; exact hA) ..).comp (measurable_const.prodMk measurable_id)
   exact ((Pond.gathered (spill I) (spill_m I) (show MeasurePreserving (swim I) X.dice (arch I X.relating) from orbit hp.posSemidef I) (settled I) hz hm').symm)
end YM.Frontier.Tuning.LocalContour
