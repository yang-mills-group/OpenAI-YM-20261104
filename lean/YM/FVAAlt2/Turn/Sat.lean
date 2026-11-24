import YM.FVAAlt2.Turn.Trust
/-! Use native micro-recursive kernel to establish at once all commutativity in marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Town
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color Book _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve High Detect Domain Tone Tone.Frame Momentum Outlook
open _root_.YM.MS.Wind _root_.YM.MS.City Native Native.Wilsonian
open Motions
open scoped Topology BigOperators ContDiff Interval
set_option linter.unusedSectionVars false
variable {G:Gauge} {I E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m n k:ℕ}{r h x:ℝ}
variable (s:Signed)
variable {F H U : Wind.Flow G}{A W:Law G}
local notation "κs"=> flagS (m:=0) (hand s⁻¹) G
local notation "S"=> turnW G s
local notation "ξ"=> tagSmooth E (BH G) QP

lemma tagC_smooth (w: tagSmooth E (BH G) QP) (f:E→ℝ) (hh:TouchF F)(h:ContDiff ℝ ∞ f)(hw: Heat.Trail w): ContDiff ℝ ∞ (fun y:E=> S (F (f y)) (walk0 w y)):=by
  simp_rw [certA]; let T:= tagSmooth E (BH G) QP
  let k:=s⁻¹; let v:T:= w.map fun i=>(passN k i.1, k.act ∘ i.2); have he(y:E): (walk0 w y).map (permute s⁻¹)=walk0 v y:= by unfold walk0 v; rw [List.map_map,List.map_map]; congr! 1
  have hv:Heat.Trail v:= by rintro i hi; obtain ⟨a,ha,rfl⟩:= List.mem_map.mp hi; exact (hand k).turn.contDiff.comp (hw a ha)
  have hx(y:E): SideS s⁻¹ (walk0 w y)=(w.map (tick s⁻¹ ∘ Prod.fst)).prod:= by unfold SideS walk0; rw [List.map_map]; rfl
  simp_rw [hx,he]; exact contDiff_const.mul (hh E f v hv h)
lemma figure_X (h:TouchF F): TouchF (S ∘ F):=fun _ _ _ f w hv hh=> tagC_smooth s w f h hh hv
lemma sat_with (h:Sat A F H)(he:TouchF F): Sat (S A) (S ∘ F) (S ∘ H):= by
 refine ⟨congr_arg (S) h.1,fun t=> ?_⟩; change Zip (⇑S ∘ F) ( Wiref G _ t + S ( H t )) t; rw [show Wiref G (⇑S ∘ F) t= S (Wiref G F t) from ?_, ← map_add ]; swap; · change Heat.orbit _ _ _ = S (Heat.orbit _ _ _); simp only [LinearMap.proj_apply]; rw [finite_cc μzone (period0 _ cour0 (main_f G) (figure_X s he)),finite_cc μzone (period0 _ cour0 (main_f G) he) ]; exact Eq.symm (lower_cyc s _ _ (period0 _ cour0 (main_f G) he))
 exact fun i=> speed_mic (m:=0) (K:=hand s⁻¹) ( h.2 t ) i
lemma rides_rank {v:ℤ}(he:_root_.YM.MS.Wind.Rank F v): _root_.YM.MS.Wind.Rank (( S ) ∘ F) v:= fun t=> moves_rank (m:=0) (K:=Γx s) (he t)
-- Weakest caller of PM type (and uniqueness), permitting finite linear moves. No bogus stability & no new comparison assumption.
variable {p:Program.Team} {u:ℤ} (P X Y:Dec G)(φ ψ:Actor G)
local notation "PathM"=> _root_.YM.MS.Wind.path (1:ℝ)
structure Lobby (φ:Actor G)(P X:Dec G) : Prop where
   touch n x : TouchF (X n x)
   rank n x : ∃ r, Wind.Rank (X n x) r
   sat n x : Sat (Tone.run (φ x n)) (X n x) (PathM n 0 P X x)
variable {φ ψ P X Y}
lemma foyer (h:PM φ P X u): Lobby φ P X:= ⟨fun i j=> ((h.owes i).stay j).joint,fun i x=>(h.owes i).pay.elim fun r hr=>⟨ (r:ℤ),hr x ⟩, h.recu⟩
namespace Lobby
lemma unique (hx:Lobby φ P X)(hy:Lobby φ P Y) : X=Y:=by
   funext n y; induction n using Nat.strong_induction_on generalizing y with
   | h n ih=>
       let K:=PathM n 0 P X y; have hb: PathM n 0 P X= PathM n 0 P Y:= path_eq 1 n 0 (fun _ _=>rfl) (fun i hi=>funext fun j=> ih i (path_in hi).2 j) -- replace
       obtain ⟨r,hr⟩:=hx.rank n y; obtain ⟨t,ht⟩:= hy.rank n y; let F:= X n y; let H:= Y n y
       have hv:=hx.sat n y; have hu:= hy.sat n y; rw [← hb] at hu;
       apply sub_eq_zero.mp; apply Dtotal;
       · refine ⟨ ?_,⟨ _ ,Rank.sub (Rank.pay (h:=hr) le_sup_left) (Rank.pay (h:=ht) le_sup_right) ⟩, fun t w _=>?_ ⟩; · rw [sub_eq_add_neg]; have he := (hx.touch n y).add (TouchF.scale (-1:ℂ) (hy.touch n y)); convert! he using 1; ext; simp -- danger
         convert! (hv.2 t w).sub (hu.2 t w) using 1; rw [map_sub]; simp only [Pi.sub_apply,Pi.add_apply]; abel -- align
       rw [Pi.sub_apply,hv.1,hu.1,sub_self]
lemma plus (hx:Lobby φ P X)(hy:Lobby ψ P Y) : Lobby (φ+ψ) P (X+Y):= by
 refine ⟨fun i y=> (hx.touch i y).add (hy.touch i y),fun i y=>?_ , fun i y=>?_ ⟩; · obtain ⟨r,hr⟩:= hx.rank i y; obtain ⟨t,ht⟩:=hy.rank i y; exact ⟨r ⊔ t, (hr.pay le_sup_left).add (ht.pay le_sup_right)⟩
 obtain he:=hx.sat i y; obtain hv:=hy.sat i y; simp only [Pi.add_apply,map_add]; refine ⟨ congr_arg₂ (·+·) he.1 hv.1, fun t=>?_ ⟩
 have ht : PathM i 0 P (X+Y) y t= PathM i 0 P X y t + PathM i 0 P Y y t:= by simp_rw [Wind.path,one_smul,Finset.sum_apply, Pi.add_apply, map_add,Pi.add_apply, Finset.sum_add_distrib]; -- eta
 rw [ht,map_add,Pi.add_apply, add_add_add_comm]; exact Zip.add (he.2 t) (hv.2 t) -- derivative address template check
lemma static (hx:Lobby φ P X)(c:ℂ): Lobby (c • φ) P (c • X):= by
 refine ⟨fun i x=> TouchF.scale _ (hx.touch i x), fun i x=>(hx.rank i x).elim fun r hr=> ⟨ r,hr.smul _ ⟩,fun i y=> ?_⟩; obtain he:= hx.sat i y; simp only [Pi.smul_apply,map_smul]; refine ⟨congr_arg (c • · ) he.1, fun t=>?_⟩
 simp_rw [show PathM i 0 P (c • X) y t=c • PathM i 0 P X y t from by simp only [ Wind.path,one_smul, Finset.sum_apply, Pi.smul_apply,map_smul, Finset.smul_sum ] ]; rw [map_smul,Pi.smul_apply, ← smul_add]; exact Zip.scalar (he.2 t) c
lemma zero (P:Dec G): Lobby 0 P 0:= ⟨fun _ _=> TouchF.zeros, fun _ _=> ⟨_,Rank.zero G 0⟩, fun n x=> ⟨ (map_zero Tone.run).symm, fun t w=>by simp only [Wind.path,one_smul, Finset.sum_apply,Pi.zero_apply, map_zero,Finset.sum_const_zero, Pi.zero_apply,add_zero]; exact hasDerivAt_const ..⟩ ⟩
lemma fin {X:I→ Dec G}{φ:I→Actor G} (s:Finset I)(h:∀ i∈s,Lobby (φ i) P (X i)): Lobby (∑ i∈s,φ i) P (∑ i∈s,X i):=by classical induction s using Finset.induction with| empty=> simpa using zero (G:=G) P| insert i s hi ih=> rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i (by simp)).plus ( ih fun j hj=> h j ( Finset.mem_insert_of_mem hj ))
end Lobby
variable (φ)
abbrev trailer (s:Signed)(P:Dec G): Dec G:= fun n x=>(turnW G s) ∘ P n x
def promoteT (s:Signed)(G:Gauge): Actor G→ₗ[ℂ] Actor G where
 toFun v h x:= Orient.pose s (v h x)
 map_smul' c f:= funext fun i=> funext fun j=> map_smul _ c (f i j)
 map_add' f g:= funext fun i=> funext fun j=>map_add _ (f i j) (g i j)
variable {φ}
lemma burning_sat (p:Program.Team)(h:PC G p P)(t:Lobby φ P X): Lobby ( promoteT s G φ ) P (trailer s X):= by
 refine ⟨ fun i y=> figure_X s (t.touch i y), fun i y=> ( t.rank i y ).elim fun r hr=> ⟨_,rides_rank s hr⟩,fun n x=>?_⟩;
 convert! sat_with s (t.sat n x) (t.touch n x) using 1
 · exact poseXY s _
 funext t; unfold Wind.path; simp_rw [one_smul,Finset.sum_apply]; simp only [Function.comp_apply,Finset.sum_apply,map_sum]; refine sum_congr rfl fun i _=>?_ ; exact (woods s t _ _ (((h.owes _).stay x).stand t rfl)).symm
-- PM comparison.Soft
variable (ψ) in
lemma PM_bill (he: PM ψ P Y u)(hb:Lobby φ P X)(h:φ=ψ): X=Y:= hb.unique (h ▸ foyer he) -- h ▸ via rhs? inspect
end YM.MS.FVA.Town
