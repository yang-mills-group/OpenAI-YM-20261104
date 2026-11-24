import YM.FVAAlt2.Shop.Graph
import YM.SchemeConversionRG11.FirstW.Mark.Root
import YM.SchemeRG11.Saddle.Arch
/-!
# Literal land stencils of `Pert.Full` regulator
This auxiliary regulator is used for the first-order Peal calibration. No Peal data
assumed as a new hypothesis of lattice-MS conversion. Here prove the Root leg is a
finite genuine stencil, all-period cylinder. For invariant-polynomial inputs implied gauge requirement proved afterwards.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Lattice Finset Filter Function Wilson Source Labels
open MS MS.Koszul MS.Cylinder MS.Native MS.Book MS.Plane
open Pert Pert.Orb MS.Cylinder.Lab
open scoped ContDiff BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}
local notation "I₀"=> Edge Cover
local notation "J"=> Lattice.Links ℤ G.El
local notation "K"=> Key G
local notation "P"=> CoverConfig G
abbrev element (b:K)(o:Four ℤ)(U:P):= (Labels.axes G b.1).coord b.2 (Bare.tensorJet 1 U o b.1)
abbrev unitLeg (b:K):= element b 0
abbrev legAt (b:K)(o:Site n)(U:Config G n) := (Labels.axes G b.1).coord b.2 (Bare.tensorJet 1 U o b.1)
open RG11.FirstW (pointU patch trace_ride tensor_front)
def roundwalk (s:Signed)(k:ℕ)(r:Fin k→Axis)(v: Finset (Fin k))(i b: Axis): Walk:= (RG11.FirstW.patch (Bare.walk r v) i b).map (·.rotate s)
lemma ortho_trip {X:Type} [AddCommGroup X][One X](s:Signed)(k:ℕ)(U:Lattice.Links X G.El)(o:Four X) (r:Fin k→Axis)(v:Finset (Fin k))(i b:Axis):
   Bare.plateU (Lattice.pull s 0 U) (Lattice.affine s⁻¹ 0 o) (Bare.walk r v) i b=G.curvature (travel U o (roundwalk s k r v i b)):=by rw [←trace_ride,travel_pull]; simp [Lattice.affine,roundwalk]
-- all the links (including transports) through the height of one root leg
abbrev addresses (k:ℕ):= Signed × (Fin k→Axis) × Finset (Fin k) × Axis × Axis
def stages(x:Cover): Walk → Finset (Edge Cover)
 | []=>∅
 | d::w=>insert (d.used x) (stages (x+d.vec) w)
lemma locStages (U V:P)(x:Cover)(w:Walk)(he:∀ e∈stages x w,U e=V e) : travel U x w=travel V x w:=by
 induction w generalizing x with
 | nil=>rfl
 | cons d w ih=> rw [travel, travel,ih _ (fun u hu=>he u (mem_insert_of_mem hu)),Step.read,Step.read, he (d.used x) (mem_insert_self ..) ]
def sites (k:ℕ) := univ.biUnion (fun i:addresses k=> stages 0 (roundwalk i.1 k i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2))
lemma uses_leg (u:K)(U V:P)(he:∀ e∈sites u.1,U e=V e): unitLeg u U=unitLeg u V:=by
 have H(s:Signed)(w: Fin u.1→Axis)(p: Finset (Fin u.1))(i j:Axis): travel U 0 (roundwalk s u.1 w p i j)=travel V 0 (roundwalk s u.1 w p i j):=locStages U V 0 _ (fun e hz=> he e (Finset.mem_biUnion.mpr ⟨(⟨s,w,p,i,j⟩:addresses u.1),mem_univ _,hz⟩))
 have hv (s:Signed): Bare.diffU u.1 (Lattice.pull s 0 U) (Lattice.affine s⁻¹ 0 0)=Bare.diffU u.1 (Lattice.pull s 0 V) (Lattice.affine s⁻¹ 0 0):=by
   funext i j r; simp only [Bare.diffU,ortho_trip,H]
 simp only [unitLeg, element,Bare.tensorJet,Bare.oval,Bare.rawJet,hv]
lemma uses_wrap (u:K)(U:Config G n)(o:Site n): unitLeg u (expandAt o U)=legAt u o U :=by
 have h(s:Signed): Bare.diffU u.1 (Lattice.pull s 0 (expandAt o U)) (Lattice.affine s⁻¹ 0 0)= Bare.diffU u.1 (Lattice.pull s 0 U) (Lattice.affine s⁻¹ 0 o):=by funext i j p; simp only [Bare.diffU,ortho_trip,travel_at,map_zero,zero_add]
 simp only [unitLeg,element, legAt,Bare.tensorJet,Bare.oval,Bare.rawJet,h]
-- Actual Taylor germs in log-link variables. Proof doesn't use Eq of projections.
variable (u:Key G)
abbrev paper (k:ℕ) := ↥(sites k)
abbrev Q := Lot G (paper u.1)
set_option linter.unusedSectionVars false
local notation "qK"=> Q u
/-- extend log chart by exactly the missing links; CLM only on each component. -/
def rail (k:ℕ) (p:I₀) : Lot G (paper k)→L[ℝ] G.Color := if hz:p∈sites k then ContinuousLinearMap.proj ⟨p,hz⟩ else 0
def point (U:qK):P:= fun p=> G.lieExp (rail (G:=G) u.1 p U)
def written (U:qK):ℝ:= unitLeg u (point u U)
lemma rail_yes (p) (hz:p∈sites u.1) (U:qK): rail u.1 p U=U ⟨p,hz⟩:=by rw [rail,dif_pos hz];rfl
lemma stencil_is (a:Lattice.Links ℤ G.Color): unitLeg u (G.lieExp ∘ a)= written u (fun k=>a k.val):=uses_leg _ _ _ fun l h=>by rw [point,rail_yes]; exacts [rfl,h]
lemma letter_jet (v:Walk)(x:Cover): ContDiff ℝ ω (fun a:qK => G.mat (travel (point u a) x v)):=by
 induction v generalizing x with
 | nil=>exact contDiff_const
 | cons d v ih=>
   simp only [travel,G.mat_mul]; apply ContDiff.mul _ (ih _); let L:=rail (G:=G) u.1 (d.used x); have he: ContDiff ℝ ω (fun U:qK=> G.mat (point u U (d.used x))):= G.exp_jet.comp (f:=L) L.contDiff
   unfold Step.read; split; · exact ( (starL ℝ).contDiff.comp he )
   exact he
lemma tensorBorn (s:Signed) : Taylor.germ (fun U:qK=> Bare.diffU u.1 (Lattice.pull s 0 (point u U)) (affine s⁻¹ 0 0)):=
 contDiffAt_pi.mpr (fun i=> contDiffAt_pi.mpr (fun k=> contDiffAt_pi.mpr (fun p=> by
   simp only [Bare.diffU,ortho_trip]; exact (ContDiff.const_smul _ (ContDiff.sum (fun w _ => (Bare.curve_diff (letter_jet u (roundwalk s _ p w i k) _)).const_smul (Bare.sign w)))).contDiffAt ))) -- maybe shadow pull
set_option maxRecDepth 8000 in
lemma born : Taylor.germ (written u):=by
 let L:Labels.Taylor G u.1 →L[ℝ] ℝ:= ((Labels.axes G u.1).coord u.2).toContinuousLinearMap
 let S(s:Signed): Bare.Response G u.1 →L[ℝ] Labels.Taylor G u.1:= (Labels.Taylor.turn s.ortho ∘ₗ Bare.radialMap).toContinuousLinearMap
 have he(s:Signed): Taylor.germ (fun U:qK=> Bare.oval s 1 (point u U) 0 u.1):=by
   simp only [Bare.oval,Bare.rawJet,one_zpow,one_smul]; exact (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Bare.Response G u.1) (F:=Labels.Taylor G u.1) (S s)).contDiffAt.comp (f:=fun U:qK=> _) 0 (tensorBorn u s)
 have ht:=ContDiffAt.sum (x:=(0:qK)) (s:=Finset.univ) (f:=fun s U=> Bare.oval s 1 (point u U) 0 u.1) (fun s _=> he s)
 have hv:=ContDiffAt.const_smul ((Fintype.card Signed:ℝ)⁻¹) ht
 exact (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Labels.Taylor G u.1) (F:=ℝ) L).contDiffAt.comp (f:=fun U:qK=> Bare.tensorJet 1 (point u U) 0 u.1) 0 hv
def origin : Dot G Cover:= Sew.art (fun e:paper u.1=>e.val) (written u)
lemma roots_co (n:Side):
  Native.Studio.Reads (shown n (origin u)) (legAt u (0:Site n)):= by
 let R: Chart.City G (Site n)→L[ℝ] qK:= Sew.pull (Sew.thread (wrap n) (fun e:paper u.1=>e.val)); have he : legAt u (0:Site n) ∘ Chart.nation= written u ∘ R:=by -- typo
   funext x; let a:Lattice.Links ℤ G.Color:=fun p=> x (wrap n p.1,p.2); rw [Function.comp_apply,← uses_wrap]; rw [show expandAt 0 (Chart.nation x)=G.lieExp ∘ a from funext (fun p=>by simp only [a,Chart.nation,expandAt,add_zero,Function.comp_apply]), stencil_is]; rfl
 refine ⟨?_,?_⟩; rw [he]; exact ContDiffAt.comp (f:=R) 0 (by rw [map_zero]; exact born ..) R.contDiff.contDiffAt
 rw [he]; exact Sew.enters_gorge _ _ (born u)
lemma price_phase : Tuned (origin u) 0 := Tune_port _ _ (born u)
lemma first : From (origin u).val 1 :=by
 intro l H; obtain rfl:l=[]:= List.length_eq_zero_iff.mp (by omega); suffices written u 0=0 by simp [origin,Sew.art,Cylinder.region,this]
 have e : point u 0=expandAt (0:Site 4) (positiveLinks (0:Potential G 4)):=by funext; simp [point,expandAt]
 unfold written; rw [e,uses_wrap]; simp [legAt]
end YM.FVAAlt2.Pairing
