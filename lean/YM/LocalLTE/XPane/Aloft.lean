import YM.LocalLTE.XPane.Shoe
import YM.MergeProof.Cashew
import YM.MergeProof.Domino
import YM.MergeProof.Hens
import YM.MergeProof.Wicket
import YM.MergeProof.South.Admit
/-!
# Agency sheet.Evaluation of a printed spectral proxy.We establish also
at and off the exceptional set.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Bandage Mallow
open YM.MergeProof YM.LocalLTE.Vinca YM.LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.XPre
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open MergeProof.Menu Marker Accent Overlay Push Pressure ConnectedActivityE6 Push.AbsoluteSums MeasureTheory
section
variable {I:Type} [DecidableEq I][Fintype I] (B:Census I){G:Gauge}
-- passive pattern.App at axes zero with real.F redundancy. X.
variable (A:History G)(m n N d:ℕ)
set_option quotPrecheck false
local notation "T₀"=> ((Labels.frames G).level d)
local notation "B'"=> localSection G d
local notation "S"=> A.levels.clock.op m n
local notation "R"=> A.rep N n (m+1)
local notation "Q"=> A.rep N n m
variable (P:Extra.Histories.Music ((Labels.frames G).level d) A N n)
    (W:Bid.Worth) (F:I→((Labels.frames G).level d).Coeff)(x:I→Site (A.S.side (m+1) n))(ξ:I→ℝ)
local notation "Φ"=> P.tone (m+1)
local notation "Ψ"=> P.tone m
local notation "z"=> (((A.S.block m).val:ℂ)^d)
noncomputable abbrev slabF : Config G (A.S.side (m+1) n)→ Marker.Poly B := Accent.restore R (fun i=> ((Φ).plays (F i)).exponentialEntry 0 B' R) (fun i=> profile (R).activities ((Φ).plays (F i)).forced) (fun _ _=>0) (fun _ _=>0)
local notation "X"=>Harmonics.slabF B A m n N d P F
local notation "o"=> fun _: I=> (0:Site (A.S.side (m+1) n))
local notation "v" i => ((Φ).plays (F i))
local notation "q" i=> ((Ψ).plays (F i))
omit [Fintype I] in
private lemma towedNil {i:Type}[Finite i]{Y:Type}{s:Side}(l:i→Support s)(e:ℝ)(b:ℕ):Towed ξ l (fun _ _=> (0:Poly B)) (Y:=Y) b e 0:=by
       refine ⟨0,Summable.of_finite,fun i=> ?_,fun i=>⟨0,fun i=>le_rfl,fun _ _=>?_ ,?_⟩⟩
       · simp_rw [Pi.zero_apply,zero_mul,ite_self]; exact ⟨fun _=>le_rfl,summable_zero, by simp⟩
       · change ‖(0:ℂ)‖≤0; rw [norm_zero]
       simp [GridApprox.Nil.wordsPrice]
-- valuation.Parker validation; derivatives stored separately.
include ξ
lemma slab_entry (hm:m<N)(h:A.Selected)(hr:Heard (localSection G d) A N n (hol G) (m+1) (P.tone (m+1))) U: (∀ i,(slabF B A m n N d P F U).part (B.fire i)=(v i).density 0 B' R U)∧(slabF B A m n N d P F U).part B.quiet=(R).eval U:=by
   let F₀(i):=(v i).forced
   have hp: Served R (fun i=> (v i).exponentialEntry 0 B' R) (fun i=> profile (R).activities (F₀ i)) X (o) ξ 0 0:=by
       refine ⟨(fun _ _=>0),(fun _ _=>0),⟨fun i=>⟨?_,fun _ _ h=>(h rfl).elim⟩,fun i=> ⟨?_,fun _ _ h=>(h rfl).elim⟩⟩,towedNil _ ξ _ _ _,towedNil _ ξ _ _ _,rfl⟩
       · exact ⟨⟨fun _ _ _ _=> rfl,fun _ _=>rfl,fun _=>measurable_const,fun _ _ _=>rfl⟩,fun U h=> (h rfl).elim,fun _=>rfl⟩
       exact ⟨⟨fun _ _ _ _=> rfl,fun _ _=>rfl,fun _=>measurable_const,fun _ _ _=> rfl⟩,fun U h=>(h rfl).elim⟩
   obtain ⟨hT,hK⟩:= hp.relay (fun i=> rem_dominated (hr.earns (F i)|>.2)) (h.represents N n (m+1) hm).good.labels U; exact ⟨fun i=>(hT i).trans (congr_fun (coin_primary ..) U),hK⟩
lemma slab_transport {l:Type}[Fintype l](P₀:l→Menu.Hat B (A.rep N n (m+1))) (v₀:I→ℂ)(hΩ:∀ V,X V=Poly.pass (Mach B v₀) * Expense P₀ ξ S V) (hm:m<N)(h:A.Selected)(hr:Heard (localSection G d) A N n (hol G) (m+1) (P.tone (m+1)))(hP:Responds (localSection G d) A N n W m (P.tone (m+1)) (P.tone m)) : Integrable (slabF B A m n N d P F) (prior G _) ∧ ∀ i U, (((S).push (R).beta X U).part (B.fire i))= coin Q ((z)⁻¹ • ((q i).exponentialEntry 0 B' Q)) ((z)⁻¹ • ((q i).forced)) U:=by
   let V:= Φ; let K:= R; let m':= Poly.pass (Mach B v₀)
   have h0:=h.represents N n (m+1) hm; have hi: Integrable (X) (prior G _):=by
      rw [show X=(fun _=>_) from funext hΩ]
      let L : Poly B →ₗ[ℂ] Poly B := {toFun:=(m'*·), map_add':= fun u vV=>mul_add m' u vV, map_smul':=fun t x=> mul_smul_comm ..}
      let T:= (L.restrictScalars ℝ).toContinuousLinearMap
      exact T.integrable_comp (heat P₀ S ξ h0.good)
   refine ⟨hi,fun i=>?_⟩
   have he:(z)≠0:=by exact pow_ne_zero _ (by exact_mod_cast ((A.S.block m).2.ne' :_)) -- Side=0 <; lemma? 
   have h' : (fun U=> (((S).push (R).beta X U).part (B.fire i)))= coin Q ((z)⁻¹ • ((q i).exponentialEntry 0 B' Q)) ((z)⁻¹ • ((q i).forced)):=by
      rw [push_get (A.levels.transition_mass ..) hi, show (fun U=> ((X U).part (B.fire i)))=(v i).density 0 B' (R) from (funext fun U=>Harmonics.slab_entry B A m n N d P F ξ hm h hr U|>.1 i), coin_mul, coin_primary, hP.values]
      unfold Extra.Histories.blast
      rw [smul_smul,inv_mul_cancel₀ he,one_smul]
   exact fun U=> congr_fun h' U
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
