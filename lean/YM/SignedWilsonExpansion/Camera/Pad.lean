import YM.SignedWilsonExpansion.Chron.Fares
import YM.SignedWilsonExpansion.Stage.Cluster
import YM.SignedWilsonExpansion.Kane.Finale
/-!
# The purchased pad of finite compacts; accumulation relative to them on f
Parametric in the path.Contraction.N.Post.Edge.These quotes are consumed by Shutter.Receive.
-/
set_option autoImplicit false
set_option maxHeartbeats 530000
noncomputable section
namespace YM.SignedWilsonExpansion.Camera
open Function Set Filter MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East Pert.Scale Maxwell Extra.FD PhysicalNext.Repeat.Legato Run Lattice FullVolume Cells Homes
open XSpace Commission Dancer Dancer.Motif Dancer.Supper Dancer.Drawing Asymptotics Dancer.Stitch
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK WilsonCoeffUV.Bank PathCost
open Wilson RG PowerSeries Purchases UVClock PurchVoice Schedules HalfRoof HalfRoof.Minty WardBin Source Labels Normalize
open FVA2 FVA2.Dframe SeatsW Dancer.Shell Dancer.Fort XSpace.Cirrus
open Kane.Tilted Belle Belfry Belfry.ScaleFits StageG
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {d n :ℕ}{X:Initialize G}{ι β:Type}{ℱ:Filter ι}{L: Filter β}{A:Credit} {S:Schedule}
abbrev Scale (n:ℕ):= FVA2.Scale.Stage n
local notation "Θ" => Set (Points n)
structure Pad (n:ℕ) where
   F : Set (Points n)
   roi : Path.Roi F
   leader : ∃ x:Points n,F∈ 𝓝 x
abbrev zone (U:Pad n):= U.F
abbrev withinP (u:Pad n)(x:Points n): Prop:= u.F∈ 𝓝 x
variable (U:Pad n)(C:Family G)
lemma anchor (Q: Θ) (s:Path.Roi Q) (v:Points n)(h:v∈conf n):∃ U:Pad n,Q⊆interior U.F∧ withinP U v:=by
   let A:= insert v Q; have hp:IsCompact A:=s.1.insert v; obtain ⟨ε,p,r⟩:= Integration.Cope.padded hp ( insert_subset h s.2 ); let P:=Metric.cthickening ε A; have hu : A⊆ interior P:=by exact Subset.trans (Metric.self_subset_thickening p _) (interior_maximal (Metric.thickening_subset_cthickening ..) Metric.isOpen_thickening)
   have hv:P∈𝓝 v:= mem_interior_iff_mem_nhds.mp ( hu ( mem_insert .. ) ); exact ⟨⟨ P,⟨hp.cthickening,r⟩,v,hv⟩, (subset_insert v Q).trans hu,hv⟩
-- guard permits all corners. finite after fixed r. payment at corner by extrap.
variable (r:ι→ℝ) (f:ι→ℕ) (x:ι→ Fin n→ Cover)
abbrev sizeP (S:Schedule)(i:ι) := S.a (f i)/ r i
abbrev plot (S:Schedule)(i:ι):Points n:= Extraction.tag ( sizeP r f S i ) (x i)
-- induction lemma relative tag & Φ certificate
abbrev pad0 (ℱ:Filter ι)(i:Schedule): Prop:= ∀ᶠ z in ℱ, plot r f x i z∈ zone U
lemma office (i:ι)(hp:0<r i): r i • plot r f x C.S i= Order.grid C (f i) (x i):=by
    apply PiLp.ext; intro j; apply PiLp.ext; intro a
    change r i*((C.S.a (f i) / r i)*(x i j a:ℝ))= C.S.a ( f i )*(x i j a:ℝ); field_simp
-- Peak Pad selection independent of outer regulators. Need general l including atTop. path x always legitimate.Input Price Q_A
abbrev Shake := Fin n→ Cover
lemma f_round {x:ι→Fin n→ Cover}{ℱ:Filter ι}{v : Points n}(hu: withinP U v) (h : Tendsto (plot r f x S) ℱ (𝓝 v)) : pad0 U r f x ℱ S:= h.eventually hu
lemma pad_round {S:Schedule}{v : Points n}(hu: withinP U v) (hr:∀ᶠ i in ℱ,0<r i)(u:Tendsto (sizeP r f S) ℱ (𝓝 0)) : ∃ x:ι→ Shake (n:=n),pad0 U r f x ℱ S∧ Tendsto (plot r f x S) ℱ (𝓝 v):=by
    let x(i):= Extraction.address ( sizeP r f S i ) v; let e(i):= plot r f x S i; have he:Tendsto e ℱ (𝓝 v) := by
        have h:Tendsto (fun i=> (4*n:ℝ)*sizeP r f S i) ℱ (𝓝 0):= ( mul_zero (4*n:ℝ) ) ▸ u.const_mul _
        apply Metric.tendsto_nhds.mpr; intro a ha; filter_upwards [ hr,h.eventually_lt_const ha ] with i hi hp; exact lt_of_le_of_lt (Extraction.approximate ( div_pos (S.a_pos _) hi ) _) hp
    exact ⟨ x,f_round U r f hu he,he ⟩
noncomputable def postage (U:Pad n) (z:Points n): Scale n:= if h:z∈ U.F then ⟨ z,U.roi.2 h ⟩ else ⟨ U.leader.choose,U.roi.2 (mem_of_mem_nhds U.leader.choose_spec) ⟩
abbrev stageP (M:Schedule) (i:ι) : Scale n:= postage U (plot r f x M i)
include x
lemma stamp_p (h:pad0 U r f x ℱ C.S) : (fun i=>(stageP U r f x C.S i).1)=ᶠ[ℱ] plot r f x C.S:= h.mono fun i hi=> by simp [stageP, postage, (show plot r f x C.S i ∈ U.F from hi)]
local notation "𝒳" => ℱ.curry L
omit x
lemma soughtP (U : Pad (n+1)) (x:ι→ Shake (n:=n+1)) (h:pad0 U r f x ℱ C.S){e:ℕ}{R:Realm G (e+1) Credit.leanC}(U₀:R.draws=C.path.levels): Sought (r∘Prod.fst) 𝒳 R (f ∘Prod.fst) (x ∘Prod.fst) ((stageP U r f x C.S) ∘ Prod.fst) U.F:=by
    have p: Tendsto Prod.fst 𝒳 ℱ:= tendsto_fst.mono_left curry_le_prod; refine ⟨ U.roi.1,U.roi.2,?_⟩; filter_upwards [ p.eventually ( ( stamp_p U C r f x h ).and h ) ] with v hv; rcases v with ⟨i,j⟩; change (stageP U r f x C.S i).1=Garden ( hereD R.draws r f i ) (x i) ∧ (stageP U r f x C.S i).1∈ zone U; change (stageP U r f x C.S i).1=plot r f x C.S i ∧ plot r f x C.S i ∈ zone U at hv; obtain ⟨hp,hV⟩:=hv
    constructor
    · rw [hp, plot]; rw [U₀]; rfl
    rw [hp]; exact hV
-- Uniform phase application. diag proof on outer path and all finite guards at fixed r. not Freak hypothesis. use choose default on pad_round.
variable (xQ:ℱ.NeBot)
lemma allP (hV:Tendsto (sizeP r f S) ℱ (𝓝 0))(hr:∀ᶠ i in ℱ, 0< r i)(T :∀ i:ι, β→ Shake (n:=n)→Prop) (p:∀ x:ι→ Shake (n:=n),pad0 U r f x ℱ S→ ∀ᶠ i:ι×β in ℱ.curry L,T i.1 i.2 (x i.1)) : ∀ᶠ i:ι×β in ℱ.curry L,∀ x:Shake (n:=n), Extraction.tag ( sizeP r f S i.1 ) x∈ zone U→ T i.1 i.2 x:= by
    let A(i:ι):Set (Shake (n:=n)):= {y| Extraction.tag ( sizeP r f S i ) y∈ zone U }
    let Q(i):=∃ y:A i,¬ ∀ᶠ u in L,T i u y.val; obtain ⟨x,hx,-⟩:= pad_round U r f U.leader.choose_spec hr hV; let z(i:ι):= if h:Q i then ( Classical.choose (show ∃ y:A i, _ from h)).val else x i
    have hu:∀ᶠ i in ℱ,∀ᶠ p in L,T i p (z i):= p z (hx.mono fun i hi=> (show z i∈ A i from (by unfold z; split; exact (_ : A i).property; exact hi )))
    refine eventually_curry_iff.mpr (?_); filter_upwards [hu,hr] with i hi hv; have H: ¬ Q i:=by
       intro u; apply (Classical.choose_spec u); rwa [show z i= _ from dif_pos u] at hi
    have hZ: (A i).Finite:= Integration.Cope.finite_mesh U.roi.1 (div_pos (S.a_pos _) hv); exact ( ( eventually_all_finite hZ ).mpr (fun j hk=> by by_contra h; exact H ⟨ ⟨j,hk⟩,h⟩))
end YM.SignedWilsonExpansion.Camera
