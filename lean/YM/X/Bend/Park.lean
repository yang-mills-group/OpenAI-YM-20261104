import YM.X.Bend.Garland
/-!
# tLabels Love.Real convolutive tangent calibration. compact matrix.T.Real.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Lattice Wilson Next.Rank Normal LiftMark Crate Porch Rays Shelf Tot
open Maxwell Maxwell.Free Extra.FD MvPolynomial Labels Pert.Position Pert.RawLabels
open Filter Function MeasureTheory Set Reed Stems Haze Fielding PertExtension LatticePT Chir Sage Bare Tri Pulse
open scoped Topology BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {d k m n:ℕ} {q:ℕ+} {V I:Type*} {r R:ℝ}
local notation "U"=> G.ColorIndex
local notation "T"=>Tet
local notation "Q"=>PlaqAxes
local notation "K"=> (atTop:Filter ℕ)
abbrev BB (F:Frames G)(H:6≤d) : «YM».Pert.Position.E F d:= (boostB:ℂ) • deity F H
abbrev MU (F: Frames G)(H:4≤d) : YM.Pert.Position.E F d:= (boostU:ℂ) • dean F H
variable (h:6≤d)(B:Bare.Shop F)
set_option quotPrecheck false
local notation "h4"=> ((by decide:4≤6) |>.trans h)
local notation "H"=> (by decide: 6≤6) -- binds any F.Omega.
local notation "b"=>BB F h
local notation "μ"=>MU F h4
local notation "kτ"=> Bank F d
local notation "Aτ"=> pureBank F d
local notation "γ"=> par F d
lemma keeperB : physicalLabel F d b= Complex.ofReal boostB • BW G h:= by rw [BB,map_smul,deity_c]
lemma keeperU (h:4≤d) : physicalLabel F d (MU F h)=Complex.ofReal boostU • UW G h:= by rw [MU,map_smul,dean_c]
lemma primitiveB : (physicalLabel F d b).val= cleanDial G (Bpol G):= by rw [Bsp,keeperB,map_smul (cleanDial G)]; rfl
lemma primitiveU (h:4≤d) : (physicalLabel F d (MU F h)).val=cleanDial G (Upol G):= by rw [Usp,keeperU,map_smul (cleanDial G)];rfl
lemma bar_beta : (Model F).conj (hierarchy F).spin d b=b:= by
   apply physical_inj; rw [physical_real F,keeperB]; simp only [map_smulₛₗ]; rw [show realBar (BW G h)=BW G h from real_crease h standing wc vivid₁]; congr 1; simp -- κ_real.G
lemma bar_mu (h:4≤d): (Model F).conj (hierarchy F).spin d (MU F h)= MU F h:= by
   apply physical_inj; rw [physical_real F,keeperU]; simp only [map_smulₛₗ]; rw [show realBar (UW G h)=UW G h from real_crease h standing₀ vc vivid₀]; congr 1; simp
lemma lead_B : γ (deity F h)= -(deity F h):= by unfold deity par; rw [scalePol_enroll]; have ht : BW G h∈Grade (6,3):= creased h standing wc; rw [scalePol_pure F _ _ ht]; unfold sign; norm_num
@[simp] lemma signB : γ b = - b := by rw [BB,map_smul,lead_B, smul_neg]
@[simp] lemma signU (h:4≤d): γ (MU F h)= MU F h:= by unfold MU dean par; rw [map_smul,scalePol_enroll]; rw [scalePol_pure F sign (UW G h) (creased h standing₀ vc)]; unfold sign; norm_num
-- µ,B arrays.Tech.Metrics. use h general with <=.
local notation "mU"=> (by decide:4≤6)
def prices :Fin 3→ℂ:= ![(boostB:ℂ),boostU,boostU]
abbrev beaconLabels (F:Frames G)(h:6≤d)(j:Fin 3) := prices j • talent F h j
lemma mounts : beaconLabels F h=![b,μ,μ]:= by ext1 i; fin_cases i <;> rfl
lemma price_eq (t:Test 3)(V:kτ): V 3 t (beaconLabels F h)=(↑(boostB*boostU*boostU):ℂ)* V 3 t (talent F h):= by
     unfold beaconLabels; rw [MultilinearMap.map_smul_univ, Fin.prod_univ_three]; simp [prices,mul_assoc]
     -- use hf after
-- marginal projections and parity. any s along Finset entries Ext arrays.Element.psi.
lemma pulse_cost (d': Test n)(A: Bank F d){u:Fin n→Pert.Position.E F d}(i:Fin n)(hp:γ (u i)= -u i)(hs:∀j,j≠i→γ (u j)= u j)(ht:pulls (par F d) A=A) : A n d' u=0:= by
   have hh : γ ∘ u= Function.update u i (-u i) := by ext1 j; by_cases h:j=i<;> first| (subst j; rw [Function.update_self]; exact hp)|(rw [Function.update_of_ne h]; exact hs j h)
   have H': A n d' (γ ∘ u)= A n d' u:= congr_arg (fun V:Bank F d=> V n d' u) ht; rw [hh,MultilinearMap.map_update_neg,Function.update_eq_self] at H'; apply mul_left_cancel₀ (show (2:ℂ)≠0 from by norm_num); calc
      _ = A n d' u + A n d' u := by ring
      _ = A n d' u + -(A n d' u):= congr_arg _ H'.symm
      _ = _ := by ring
-- zero cast 
include B
lemma pulse_white (d': Test n){u:Fin n→Pert.Position.E F d}(i:Fin n)(hp:γ (u i)= -u i)(hs:∀j,j≠i→γ (u j)= u j): pureBank F d n d' u=0:= pulse_cost d' Aτ i hp hs B.all_par
lemma whiteB1 (t:Test 1): Aτ 1 t (fun _=>b)=0:= pulse_white B _ 0 (signB _) (by intro i hi; exact False.elim (hi (Subsingleton.elim ..)))
lemma whiteBa (t:Test 2): Aτ 2 t ![b,μ]=0:= pulse_white B _ 0 (signB _) (by intro i hi; fin_cases i<;> first|exact False.elim (hi rfl)|exact signU _)
lemma white_call (t:Test 3): Aτ 3 t (beaconLabels F h)=0:= by rw [mounts]; refine pulse_white B _ (0:Fin 3) (signB _) (fun i hi=>?_); fin_cases i <;> first| exact False.elim (hi rfl)| exact signU _
variable (hq:1<q.val)
include hq
lemma white_u (h:4≤d)(t:Test 1): Aτ 1 t (fun _=> MU F h)=0:= by
    rw [show (fun _ : Fin 1=>MU F h)= (fun i=> (boostU:ℂ) • (fun _:Fin 1=> dean F h) i) from rfl, MultilinearMap.map_smul_univ, seam B _ hq t (single_u B hq h), smul_zero]
lemma white_p (h:4≤d)(t:Test 2): Aτ 2 t (fun _=> MU F h)=0:= by rw [show (fun _ : Fin 2=>MU F h)= (fun i=> (boostU:ℂ) • (fun _:Fin 2=> dean F h) i) from rfl, MultilinearMap.map_smul_univ, seam B _ hq t (double_u B hq h), smul_zero]
end YM.PositionX.Bend
