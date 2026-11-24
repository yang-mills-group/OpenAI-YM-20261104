import YM.SignedWilsonExpansion.Dancer.Coats
/-!
# Prescription.Study limit ordering on estimator (before applying to W Neighbour Leg)
Continuum polynomial uses `Measure.start` of independent prescription. Forecasted coefficients via
`Loader` and Quote.Meets. Still need physical limit first and transport c then.R. At relative scale.Basis masks.
-/
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.SignedWilsonExpansion.Dancer.Drawing
open XSpace XSpace.Structure1 Normalize Future Gauge Filter Function Matrix MeasureTheory
open Asymptotics Shell Lights SeatsW Fort Coats Commission Maxwell Maxwell.Free Maxwell.Wick
open FVA2 FVA2.Scale FVA2.Dframe
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open WilsonCoeffUV.Mer.Xa WilsonCoeffUV.Mer.Xa.MarqueQ PorchK Crops Crops.Taught
open scoped BigOperators Topology ContDiff Classical
variable {G:Gauge}{n h m q b d:ℕ}{a:Axis}{ι:Type}{l:Filter ι}
open Commission.Gram
variable (W': Initialize G) {N: Normalize.Store G} (K: Rose.Pick N) (s:G.Simple)
variable {Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {S:Prescription (Press.portDeck G)} (P:Speed.Quoted W' K Y S)
variable (Q : Way G d)
abbrev orbit (q:ℕ)(p:Stage n)(t:ℂ): Point G d n:= ∑ i∈Finset.range (q+1),t^i • Q n p i
abbrev Print (K: Rose.Pick N)(q:ℕ)(p:Stage n)(t:ℝ)(v:Tags G d n): ℂ:= orbit (FVA2.Scale.Measure.start W' K d) q p (t:ℂ) v
lemma atW (t:ℂ)(v:Tags G d n)(T:Stage n): orbit Q q T t v=∑ i∈Finset.range (q+1),t^i* Q n T i v:= by unfold orbit; rw [_root_.sum_apply]; rfl
lemma orbit_at (p:Stage n)(t:ℂ)(v:Tags G d n): orbit Q q p t v= invoke (Q n p) q t v:=by rw [atW,invoke,timed]; exact Finset.sum_congr rfl fun i _=> by rw [Tape.archive,PowerSeries.coeff_mk]; exact mul_comm ..
variable {g:ι→ℝ}{V:Set (Points n)} {p:ι→ Stage n} {x:Stage n}
local notation "Q₁"=> FVA2.Scale.Measure.start W' K d
include P s
lemma smoothP (v:Tags G d n)(t:ℕ)(p:Stage n) : ContDiffAt ℝ ∞ (fun x=> Jury.fxt Q₁ x t v) p.val :=by
     refine (Speed.Timeframe.cash 0 K Y v p.val p.property t).congr_of_eventuallyEq ?_ -- maybe `.congr_of_eventuallyEq`
     filter_upwards [(conf_open n).mem_nhds p.property] with i hi; rw [show Jury.fxt Q₁ i= _ from Jury.exactC Q₁ ⟨i,hi⟩]; exact DFunLike.congr_fun (congr_fun (TollQ.tuner s W' K Y S 0 P (d:=d) (⟨i,hi⟩:Stage n)).symm t) v
lemma increases (v:Tags G d n)(u:d≤h)(B:Stage n)(t:ℂ): orbit Q₁ q B t v= orbit ( FVA2.Scale.Measure.start W' K h ) q B t ( Normalize.up u ∘ v ):=by
     obtain ⟨a,b,c⟩:=P.toContract.toMission.born; rw [atW,atW]; exact Finset.sum_congr rfl fun i _=> congrArg (_*·) (Measure.inherited W' K 0 Y S s a b c u n B i v)
lemma news (t:Stage n) (v:Tags G d n) : orbit Q₁ q t 0 v= scene t.val d v := by
      obtain ⟨a,b,c⟩:=P.toContract.toMission.born; rw [atW, Finset.sum_eq_single 0]; · simp only [pow_zero,one_mul, Measure.dawn W' K 0 Y S s a b c n t ]
      · intro i _ h; simp [h]
      simp
lemma via (v:Tags G d n) (hp:Tendsto p l (𝓝 x))(e:Tendsto g l (𝓝 0)): Tendsto (fun i=>Print W' K q (p i) (g i) v) l (𝓝 (scene x.val d v)):=by
      rw [← news (q:=q) W' K s P x v,atW]; simp_rw [Print,atW]; have he:Tendsto (fun i:ι=> (g i:ℂ)) l (𝓝 0):=by rw [←Complex.ofReal_zero]; exact Complex.continuous_ofReal.continuousAt.tendsto.comp e
      refine tendsto_finsetSum _ fun i hi=> (he.pow i).mul (?_); simp_rw [← Jury.exactC Q₁]; exact (smoothP W' K s P v i x).continuousAt.tendsto.comp (continuous_subtype_val.continuousAt.tendsto.comp hp)
lemma discards (p:ι→Stage n)(V:Set (Points n))(hv:IsCompact V) (hs:V ⊆ conf n)(hp:∀ᶠ i in l, (p i).val∈V)(w:Tags G d n) (y:g=O[l] (1:ι→ℝ)) : (fun i=> Print W' K q (p i) ( g i ) w)=O[l] (1:ι→ℝ) :=by
       simp_rw [Print,atW,← Jury.exactC Q₁]
       have hy:(fun i=>( g i:ℂ ))=O[l] (1:ι→ℝ):= IsBigO.trans ( g:=g ) (IsBigO.of_bound' (Eventually.of_forall fun i=> (Complex.norm_real _).le)) y
       apply IsBigO.sum; intro i _; suffices hx: (fun i'=> Jury.fxt Q₁ (p i').val i w)=O[l] (1:ι→ℝ) by simpa only[Pi.one_apply,one_pow,mul_one] using! (hy.pow i).mul hx
       let f(y:Points n):= Jury.fxt Q₁ y i w; have H:ContinuousOn f V:= fun x hx=> (smoothP W' K s P w i ⟨x,hs hx⟩).continuousAt.continuousWithinAt; obtain ⟨B,hB⟩:= (hv.image_of_continuousOn H.norm).bddAbove; exact IsBigO.of_bound B ( hp.mono fun i hi=> ( hB ( Set.mem_image_of_mem _ hi ) ).trans_eq ( by simp ) )
lemma emblem {x:ι→Stage 2}(h:Tendsto g l (𝓝 0))(p: Tendsto x l (𝓝 (⟨nodes a,nodes_conf a⟩:Stage 2))): Emblem (G:=G) (h:=d) a l (fun i=> orbit Q₁ q (x i) (g i)):=by
    constructor; intro u v; let y : Stage 2:= ⟨nodes a,nodes_conf a⟩; change Tendsto (fun i=> Print W' K q (x i) (g i) ( ![u,v] : Tags G d 2 )) l (𝓝 (scene y.val d ( ![u,v] : Tags G d 2 )) ); exact via W' K s P (d:=d) (n:=2) (x:=y) (q:=q) (![u,v]: Tags G d 2) p h
end YM.SignedWilsonExpansion.Dancer.Drawing
