import YM.Frontier6.Bouquet.Garland.Open
import YM.SignedWilsonExpansion.Sat.Pearl
set_option autoImplicit false
set_option maxHeartbeats 150000
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
open FVA2.Scale Level Maxwell.Free Future Gauge Dancer.Coats SignedWilsonExpansion.Fire
variable {G:Gauge}{d t n b:ℕ}{ι L J:Type}{ℱ:Filter ι}
open MS MS.Puff MS.High MS.Native MS.Land MS.Fleet MS.Book WilsonCoeffUV.Cosmos.Polestar Precision XSpace.Structure1
variable {c a:Axis}{e u k q h K:ℕ}
open Matrix
variable {R:PhysicalNext.Repeat.Legato.Run G}{X:Initialize G}{T:∀ h,Rays G h X.hol} {f:Extraction.Order} {S':Table R.family.book}(F:Final R.family f S')(W:ℝ→tower S') (H:(Bel R.family.book).Hierarchy) (lead:Leading F W)
variable (A: L→Shawl R.family S' ι W) {r:ι→ℝ}(hr:Tendsto r ℱ trail) (p:∀ i,0<r i) (Y:Ultrafilter (ℕ×ℕ))(Y₀:(Y:Filter _)≤ (track f).fuse)(h':∀ a:L,Shine (f:=f) W H (A a) Y r ℱ d)
variable (U:Normalize.Store G)(P:Rose.Pick U){Ω:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {J':MS.Land.Prescription (Press.portDeck G)}(Q:Speed.Quoted X P Ω J')
variable {C:Family G} (B:Plans a)(X₀:ChartRatio G)(Z':(track f).PointLimits R.family S')(z':(track f).Ordered R.family S')
variable (C0: Ribbon (R:=R) (T:=T) (f:=f) W H Y U P Q X₀ a)
namespace Ribbon
open Path Wipe Canvass
variable {F W H U P Q X₀}
variable (S₀:Shoe F W U) (s:G.Simple)
local notation "L₀" => Estate.lPersh ℱ Y
local notation "α" => needle G
local notation "Wα" => ( Date F P W )
include hr lead Y₀ Z' z' C0
variable [nB:ℱ.NeBot]
include p nB
-- statement through all mesh sectors. Consume at big & small b separately.M.Record. Includes Crown.P.Ne.Thread signature.
lemma permits : Syllabus X P L₀ (α ∘ liftV r) ( levelOf F W (liftV r) ):=by
    intro b hb d hd Y'; obtain ⟨B,h⟩:= Canvass.inhabited Y' a; obtain ⟨Q'⟩:= C0 B b d hb hd (by infer_instance) hr p r (fun i=>by have := p i; exact ⟨le_rfl,by linarith⟩); let M:= Q'.paid; obtain ⟨x,hx⟩:= M.photo lead hr Y Q'.h Z' z'; exact ⟨ M.θU,M.q,(fun i=> M.liftQ false i d),M.liftQ false,M.firmQ x,a,( M.markTh ).mono ( M.sharpen Y Y₀ ),M.needed,M.embassy lead hr Y Y₀ Q'.h Z' z' x hx false,rfl, fun i k t=> M.views lead hr Y Y₀ Q'.h Z' z' false Q'.lo h k t⟩
include S₀ s
set_option maxHeartbeats 400000 in
lemma nourished : IsEquivalent ℱ ( Wα ∘ r ) (α∘r) ∧ Classroom.Primary ℱ (levelOf F W r) X P ( Wα ∘ r ):=by
    let Z:= (Y:Filter (ℕ×ℕ)); have he:Tendsto (Prod.fst: Visual ι→ι) L₀ ℱ:= tendsto_fst.mono_left curry_le_prod; have hv:= hr.comp he; let t:= (( implicit_clock s ).conforms s ).comp hr
    have H : IsEquivalent L₀ (Wα ∘ (liftV r)) (α∘(liftV r)) ∧ Classroom.Primary L₀ (levelOf F W (liftV r)) X P (Wα∘(liftV r)) := sees lead (r:=liftV r) hv P S₀ s X Q ( t.comp he ) ( permits lead hr p Y Y₀ Z' z' C0 )
    have ht:IsEquivalent ℱ (Wα ∘ r) ( α∘r ):=by
        apply IsLittleO.of_bound; intro ε h; exact curryRec (l:=ℱ) (Y:Filter (ℕ×ℕ)) ( H.1.isLittleO.bound h )
    have hv' : Wipe.Lamp G ι ℱ ( Wα ∘ r ) (levelOf F W r) U := class_menu lead hr S₀ ( ht.symm.tendsto_nhds t )
    refine ⟨ ht, ⟨ hv', ?_, ?_ ⟩ ⟩
    · exact EventuallyEq.refl ℱ _
    intro d n b v K h ε hε; let B(i:ι):=∀ x∈K,‖levelOf F W r i d n x v- Path.mote ( FVA2.Scale.Measure.start X P d ) b x ( Wα (r i) ) v‖≤ε*‖Wα (r i)^b‖; apply curryRec (p:=B) (Y:Filter (ℕ×ℕ)); exact H.2.light _ _ b v h ε hε
omit p
private noncomputable def fence (r:ι→ℝ)(i:ι) := if 0< r i then r i else 1
omit s S₀ Y₀ lead Z' z' C0
private lemma fence_t : r=ᶠ[ℱ] fence r:= (hr.eventually self_mem_nhdsWithin).mono fun i h=> Eq.symm (if_pos h)
private lemma fence_pos (i:ι) : 0<fence r i:=by unfold fence; split_ifs with hp; exact hp; exact zero_lt_one
include s S₀ Y₀ lead Z' z' C0
lemma attained : IsEquivalent ℱ ( Wα∘r ) (α∘r) ∧ Classroom.Primary ℱ (levelOf F W r) X P ( Wα∘r ):=by
    let h:= (fence_t hr); obtain ⟨q,v⟩:= nourished lead (hr.congr' h) (fence_pos hr) Y Y₀ Z' z' C0 S₀ s; have hZ:IsEquivalent ℱ ( Wα∘r ) (α∘r):= q.isLittleO.congr' ( (h.symm.fun_comp Wα).sub (h.symm.fun_comp α) ) (h.symm.fun_comp α)
    refine ⟨hZ, ⟨ class_menu lead hr S₀ ( hZ.symm.tendsto_nhds ( ( ( implicit_clock s ).conforms s ).comp hr ) ), EventuallyEq.refl ..,?_⟩ ⟩; intro d n b u A h' ε p; filter_upwards [ v.light d n b u h' ε p,h ] with i hi hp x hx; specialize hi x hx; let J:= Wα; change ‖levelOf _ _ r i _ n x u-mote (FVA2.Scale.Measure.start X P d) b x ( J (r i) ) u‖≤ ε * ‖J (r i)^b‖; change ‖PlotW F W none (r i) d _ _ _-_‖≤ _; rw [hp]; exact hi
omit hr nB in
lemma issued : IsEquivalent trail Wα α ∧ Coupling G Wα ∧ Classroom.Primary trail (levelOf F W id) X P Wα:=by
    obtain ⟨a,b⟩:= attained lead (r:=id) (ℱ:=trail) tendsto_id Y Y₀ Z' z' C0 S₀ s; exact ⟨ a, from_timer s Wα a,b ⟩
omit hr S₀ s
lemma enrolled (p:0<d) : handheld W F d ℱ:=by
    intro r t g b0; obtain ⟨B,h⟩:= Canvass.inhabited ∅ a; let a:=d+6; let G'(i:ι):= min (max (-Real.log 2) (g i)) 0;
    let r':= fence r; let R':= jump r' G'; have z:-(Real.log 2)≤0:= neg_nonpos.mpr ( Real.log_pos (show 1<(2:ℝ) from one_lt_two) ).le; have hp:= fence_t t; have hu:= fence_pos t; have w:g =ᶠ[ℱ] G':= b0.mono fun i hi=> by unfold G'; rw [max_eq_right hi.1,min_eq_left hi.2]
    have hv(i:ι): r' i≤ R' i∧ R' i≤2 * r' i:=by
       have v:= hu i; have hz:1≤ Real.exp (-G' i):= Real.one_le_exp (neg_nonneg.mpr ( min_le_right .. )); have ht:= Real.exp_le_exp.mpr ( show -G' i≤ Real.log 2 by have hs: -(Real.log 2) ≤ G' i := le_min ( le_max_left .. ) z; linarith ); rw [Real.exp_log zero_lt_two] at ht; change _≤ r' i * _ ∧ r' i * _ ≤ _; constructor; exact le_mul_of_one_le_right v.le hz; exact (mul_le_mul_of_nonneg_left ht v.le).trans_eq (mul_comm ..) -- parse
    obtain ⟨P'⟩:= C0 B 1 a one_pos (Nat.le_add_left 6 d) (by infer_instance) (t.congr' hp) hu R' hv; obtain ⟨a',x,u,P⟩:= ( P'.paid.scouting lead (t.congr' hp) Y Y₀ P'.h Z' z' true false P'.lo P'.hi (Nat.le_add_right d 6) p ).mirror; refine ⟨ a',x,u,fun u v=> (P u v).congr' (?_) ⟩; filter_upwards [hp,w] with i hi h; unfold MergeGeometry jump; rw[hi,h]
end Ribbon
end YM.SignedWilsonExpansion.Camera
