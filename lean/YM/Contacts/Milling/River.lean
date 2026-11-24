import YM.Contacts.Milling.Basin
import YM.Contacts.Milling.TreeLaw
/-! Ward at all large (standard) tori for the rescaled *full* periodic report.
 Cutoff comparison is in its own g and keeps signed coefficient W. These
 circuits will be used on finite germ calculations before tree is forgotten.
 Derive Ward jet beyond the nonlocal presentation from actual matrix symmetry.
 No Ward positivity or assertions at continuum contacts. -/
noncomputable section
namespace YM.Contacts.Milling
open Function Set Filter Metric MeasureTheory Asymptotics
open Finset Lattice RG Wilson Precision Exterior PertExtension.Series Pulse YM.Stationary Tree
open Kale
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f: Side}{T:Ratio c f}(A:Forest T){n:ℕ}
variable {X V : Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
abbrev cap (G:Gauge)(c:Side):= ℝ × Link G c
def stamp (M:Config G f→ Config G c→ℝ) (A:Forest T) : Link G c → A.Slice G→ℝ := fun q u=> M (A.drape u) (input G c q)
def runner (M:ℝ→Config G f→ Config G c→ℝ)(A:Forest T) : cap G c → A.Slice G → ℝ := fun q=> stamp (M q.1) A q.2
structure Sensor (M:ℝ→Config G f→Config G c→ℝ) (T:Ratio c f):Prop where
     color (t:ℝ) (k:Site f→ G.El) U V: M t (Lattice.gauge k U) (Lattice.gauge (k∘T.embed) V)=M t U V
     shape t s U V: M t (pull s 0 U) (pull s 0 V)=M t U V
local notation "φ" => 𝓝[>] (0:ℝ)
variable {M:ℝ→Config G f→ Config G c→ℝ}{g:cap G c→ℝ}
lemma flash_fold (h:Sensor M T) (t:ℝ)(U:Config G f)(V:Config G c): M t (A.drape (dawn A U)) V=M t U V:= by
  rw [dawn_d]; have he:= h.color t (A.foldAt U) U V; convert he using 2; funext; simp only [Lattice.gauge,Function.comp_apply,A.fold_root,inv_one,one_mul,mul_one]
lemma winged (l: V→Link G c)(h:AnalyticAt ℝ l 0)(he:l 0=0) (x:V): ∃ d:ℝ,∀ᶠ t in φ, ‖t⁻¹ • l (t • x)‖ ≤ d:= by
   have ht := (rays_at_zero h).mpr he x -- only f ℝ? theorem generalized Y
   obtain ⟨k,hk,H⟩:= ht.exists_pos; refine ⟨k,?_⟩; filter_upwards [H.bound.filter_mono (nhdsGT_le_nhdsNE _),Tested.eventually_pos] with t hg hx; rw [norm_smul,norm_inv,inv_mul_eq_div, div_le_iff₀ (norm_pos_iff.mpr hx.ne')]; simpa using hg

def axisRoll (l:V→Link G c) : (ℝ×V)→ cap G c:=fun x=>(x.1,l x.2)
lemma sensorGate {b:ℝ}(h:Sensor M T)(hg:AnalyticAt ℝ g 0)(hc:Radial.Stationary g)(he:Sight (runner M A) g b n)
    (U Y: V→ Link G c)(hU:AnalyticAt ℝ U 0)(hZ:U 0=0)(hY:AnalyticAt ℝ Y 0)(hY':Y 0=0) (L:V → (Config G f ≃ₜ Config G f)) (hp:∀ x, Kale.released T (L x)) (hS:∀ x, Kale.released T (L x).symm) (hT : ∀ x,MeasurePreserving (L x) (prior G f) (prior G f))
    (hμ : ContinuousAt (fun x : V × Config G f=> L x.1 x.2) (0,1))(hv:ContinuousAt (fun x: V × Config G f=>(L x.1).symm x.2) (0,1))(hl : L 0 1=1)
    (hK : ∀ᶠ x in 𝓝 (0:V),∀ t a,M t (L x a) (input G c (Y x))=M t a (input G c (U x))) : Rays (n+3) ((g∘axisRoll U)-(g∘axisRoll Y)):= by
  let Q:=g∘axisRoll U; let P:=g∘axisRoll Y; have hE (V:V→Link G c)(h:AnalyticAt ℝ V 0)(he:V 0=0): AnalyticAt ℝ (axisRoll V) 0 := ContDiffAt.analyticAt (contDiffAt_fst.prodMk (h.contDiffAt.comp (f:=Prod.snd) _ contDiffAt_snd))
  have hpP : axisRoll Y 0=0 := Prod.ext rfl hY'; have hpQ:axisRoll U 0=0:= Prod.ext rfl hZ; have hP : AnalyticAt ℝ P 0 := AnalyticAt.comp (by rw [hpP]; exact hg) (hE _ hY hY'); have hQ:AnalyticAt ℝ Q 0 := AnalyticAt.comp (by rw [hpQ]; exact hg) (hE _ hU hZ)
  refine benchPitch (hQ.sub hP) fun x=> marker (hQ.sub hP) _ (sample_cost (merkin hg (rays_cast hg hc) _ (hE _ hU hZ) hpQ) (merkin hg (rays_cast hg hc) _ (hE _ hY hY') hpP) _ _ ?_)
  let y:ℝ→ Link G c:=fun t=>t⁻¹ • Y (t • x); let w:ℝ→ Link G c:= fun t=> t⁻¹ • U (t•x)
  obtain ⟨k,hk⟩:= winged _ hU hZ x; obtain ⟨r,hr⟩:= winged _ hY hY' x; have hb : ∀ᶠ t in φ, ‖w t‖ ≤ max k r ∧ ‖y t‖≤max k r:= (hk.and hr).mono fun t ht=> ⟨ht.1.trans (le_max_left ..),ht.2.trans (le_max_right ..)⟩
  let ℓ(t:ℝ): A.Slice G≃ₜA.Slice G:= swing A (hp (t•x)) (hS _); let u:= A.order G; let Φ:=φ ×ˢ (𝓝 (1:A.Slice G));
  have Hx:Tendsto (fun t:ℝ=> t•x) φ (𝓝 0):=(along x).mono_left (nhdsGT_le_nhdsNE _); have hu:Tendsto (fun x: A.Slice G=> A.drape x) (𝓝 1) (𝓝 1):=by simpa [curtain_one] using! (Forest.continuous_drape A (G:=G)).tendsto 1
  have hi:Tendsto (fun z:ℝ×A.Slice G=> (z.1 • x,A.drape z.2)) Φ (𝓝 (0,1)):= ((Hx.comp tendsto_fst).prodMk_nhds (hu.comp tendsto_snd))
  have hh:Tendsto (fun z:ℝ×A.Slice G=>ℓ z.1 z.2) Φ (𝓝 1):= by have hz:= hμ.tendsto; rw [show L _ _=_ from hl] at hz; -- unfolds?
                                                                                 exact (show Tendsto (dawn A) _ _ from by simpa using! (dawn_cont A (G:=G)).tendsto 1).comp (hz.comp hi)
  have hy:Tendsto (fun z:ℝ×A.Slice G=>(ℓ z.1).symm z.2) Φ (𝓝 1):= by
    have he:= hv.tendsto; erw [show (L 0).symm 1=1 from (L 0).symm_apply_eq.mpr hl.symm] at he; exact (show Tendsto (dawn A) (𝓝 1) (𝓝 (1:A.Slice G)) from (by simpa using! (dawn_cont A (G:=G)).tendsto 1)).comp (he.comp hi)
  have hA : ∀ᶠ t in φ, MeasurePreserving (ℓ t) (PertExtension.Chart.physical G _) (PertExtension.Chart.physical G _) ∧ runner M A (t,t•y t) ∘ ℓ t = runner M A (t,t• w t) := by
    filter_upwards [Hx.eventually hK,Tested.eventually_pos] with t he ht; refine ⟨swing_preserve _ _ _ (hT _),funext fun u=> ?_⟩; change M t (A.drape (dawn A _)) (input G c _) = M t _ (input G c _); unfold w y; rw [smul_inv_smul₀ ht.ne', smul_inv_smul₀ ht.ne', flash_fold A h]; exact he _ _
  obtain ⟨C,hC,H⟩:= shaded he hh hy w y hA hb; refine ⟨C,hC, (Tested.eventually_pos.and H).mono fun t ht=>?_⟩; have hx (f:V→Link G c): sample g (1,t⁻¹ • f (t • x)) t=sample (g ∘ axisRoll f) (1,x) t:= by unfold sample Function.comp axisRoll; rw [show t • ((1:ℝ),_)= (t • (1:ℝ),f (t• x)) from Prod.ext rfl (smul_inv_smul₀ ht.1.ne' _)]; rfl
  change ‖Real.exp _-Real.exp _‖≤ _; rw [←hx U, ←hx Y]; exact ht.2
lemma rotates (hL:Odd T.count.val){b:ℝ}(h:Sensor M T)(hg:AnalyticAt ℝ g 0)(hc:Radial.Stationary g)(he:Sight (runner M A) g b n)(s:Signed): Rays (n+3) (g-(g∘axisRoll (orderTurn s))):= by
   refine (sensorGate A h hg hc he id (orderTurn s) analyticAt_id rfl ((orderTurn s).analyticAt _) (map_zero _) (fun _=> turn f G s) (fun _=> turn_fed T hL s) (fun _=>turn_fed (G:=G) T hL s⁻¹) (fun _=> prior_pull s 0) ?_ ?_ ?_ ?_)
   · exact (Homeomorph.continuous (turn f G s)).continuousAt.comp continuousAt_snd
   · exact (Homeomorph.continuous (turn f G s).symm).continuousAt.comp continuousAt_snd
   · change pull s 0 (1:Config G f)=1; ext1 i; simp [pull,Step.read]
   refine Eventually.of_forall fun x t a=>?_ ; change M t (pull s 0 a) _ = M t a _; exact (congr_arg _ (flip_links s x).symm).trans (h.shape ..)
lemma buffers {b:ℝ}(h:Sensor M T)(hg:AnalyticAt ℝ g 0)(hc:Radial.Stationary g)(he:Sight (runner M A) g b n)(u:G.El): Rays (n+3) (g-(g∘axisRoll (stain u))):= by
   let k:= fun _:Site f=> u
   refine sensorGate A h hg hc he id (stain u) analyticAt_id rfl ((stain u).analyticAt _) (map_zero _) (fun _=> roam f k) (fun _=> roam_fed T k) (fun _=> roam_fed T k⁻¹) (fun _=> prior_gauge k) ((Homeomorph.continuous _).continuousAt.comp continuousAt_snd) ((Homeomorph.continuous_symm _).continuousAt.comp continuousAt_snd) ?_ ?_
   · ext1 i; change u*1*u⁻¹=1; group
   exact Eventually.of_forall fun x t a=> by rw [← stain_cons u x]; exact h.color t k ..
lemma costs_now {b:ℝ}(h:Sensor M T)(hg:AnalyticAt ℝ g 0)(hc:Radial.Stationary g)(he:Sight (runner M A) g b n): Rays (n+3) (g ∘ axisRoll (Prod.snd (α:=BaseSites G c))-g ∘ axisRoll (moveField (G:=G) (m:=c))):= by
   let k (x:Swatch G c):= switchSite x.1 ∘ T.parent; have hi i: Continuous (fun x=> k x i) := (continuous_apply _).comp (switch_cont.comp continuous_fst)
   refine sensorGate A h hg hc he Prod.snd moveField contDiffAt_snd.analyticAt rfl moveField_analytic moveField_zero (fun x=> roam f (k x)) (fun _=> roam_fed T _) (fun i=> roam_fed T (k i)⁻¹) (fun i=> prior_gauge (k i)) ?_ ?_ ?_ ?_
   · refine (continuous_pi (fun i=> ?_)).continuousAt; exact ((hi _|>.comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)).mul (hi _|>.inv.comp continuous_fst)
   · refine (continuous_pi (fun i=>?_)).continuousAt; exact ((hi _ |>.inv.comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)).mul (hi _|>.inv.inv.comp continuous_fst)
   · change Lattice.gauge (k 0) 1=1; ext1 i; simp [k,Lattice.gauge]
   filter_upwards [moveField_germ (G:=G) (m:=c)] with i hi t a; rw [hi,show shiftLinks i=Lattice.gauge (k i ∘ T.embed) (input G c i.2) from (by unfold shiftLinks; rw [show k i ∘ T.embed=switchSite i.1 from funext fun j => by simp [k,Ratio.embed_parent]])]; exact h.color t (k i) _ _
end YM.Contacts.Milling
