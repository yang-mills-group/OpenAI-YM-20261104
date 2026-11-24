import YM.MSbar.Rolling.Quadratic
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix Function Filter MeasureTheory Set
open Lattice Wilson RG Precision Tree Push Push.Uniform Exterior
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S: StepData c f}(B:Forest S.ratio)
local notation "∆"=> fderiv ℝ
-- native trunc p.H.Stored.Att.Head.Black ridge. use LinearMap.toMatrix' as notation
set_option quotPrecheck false
local notation "H"=> Positions (Joint B G)
local notation "X"=> Positions (Primary c G)
local notation "N"=> Positions (Primary f G)
local notation "Y"=> Positions (Key B G)
local notation "γ"=> (tint G)
-- costA frame adapters.Bond.L.R terms.
abbrev pushF : Positions (Joint B G)→L[ℝ]Positions (Primary c G) := (ContinuousLinearMap.fst ℝ X Y).comp (partSpace _ _).toContinuousLinearMap
abbrev pushG : Positions (Joint B G)→L[ℝ]Positions (Key B G) := (ContinuousLinearMap.snd ℝ X Y).comp (partSpace _ _).toContinuousLinearMap
noncomputable def stamp (G:Gauge):Positions (Key B G)→L[ℝ]Positions (Primary f G):= LinearMap.toContinuousLinearMap ({
    toFun:=fun u ⟨⟨x,i⟩,j⟩=> if h:(x,axisEquiv.symm i)∈B.trunks then 0 else u (⟨(x,axisEquiv.symm i),h⟩,j)
    map_add' u v:=by funext x; obtain ⟨⟨x,i⟩,j⟩:=x; simp only [Pi.add_apply]; split <;> simp_all
    map_smul' r u:=by funext x; obtain ⟨⟨x,i⟩,j⟩:=x; simp only [Pi.smul_apply, RingHom.id_apply]; split <;> simp } : Positions (Key B G) →ₗ[ℝ]Positions (Primary f G))
noncomputable def imageCopy (G:Gauge): Positions (Primary c G) →L[ℝ] Positions (Key B G) := LinearMap.toContinuousLinearMap ({
    toFun v i:= linearCopy S.ratio (collect G (tint G _ v)) i.1.val i.2
    map_add' v u:=by funext e; simp only [Pi.add_apply]; unfold linearCopy; split; simp; rfl
    map_smul' r u:=by funext e; simp only [Pi.smul_apply,RingHom.id_apply]; unfold linearCopy;split; simp; rfl } : Positions (Primary c G) →ₗ[ℝ] Positions (Key B G))
lemma sealShift (x: Positions (Primary c G))(y:Positions (Key B G)) (k:Key B G) : imageCopy B G x k= linearCopy S.ratio (collect G (tint G _ x)) k.1.val k.2:=rfl
lemma ruler (x:Site f)(a:Axis)(i:G.ColorIndex) (z:Positions (Key B G)): stamp B G z ((x,coord a),i)= if ht:(x,a)∈B.trunks then 0 else z (⟨(x,a),ht⟩,i):=by
    generalize he:coord a=t; change dite ((x,axisEquiv.symm t)∈B.trunks) _ _=_; have hp : axisEquiv.symm t=a:= he ▸ axisEquiv.symm_apply_apply a; subst a; rfl
local notation "V"=>fieldDir G c 1
local notation "W"=>fieldDir G f 1
open Work.F03
lemma shiftScale (x: Positions (Primary c G))(y:Positions (Key B G)) : let z:= y+imageCopy B G x
    (paint B G (meetVar x y)).1= tint G _ x ∧ Bid.stretch B (paint B G (meetVar x y))= tint G _ (stamp B G z):=by
    intro z; rw [paint_meet]; refine ⟨rfl,?_⟩; funext e; obtain ⟨i,j⟩:=e; ext l
    obtain ⟨a,rfl⟩:= axisEquiv.surjective j
    change _=stamp B G z ((i,coord a),l); rw [ruler]; simp only [Bid.stretch,axisEquiv.symm_apply_apply]; split
    · rename_i ht; rw [linearCopy,if_pos (B.trunk_internal ht),zero_add]; rfl
    next hx=>
       simp only [PiLp.add_apply]
       change (_:ℝ)+_= (_:ℝ)+_; rw [add_comm]; rfl
lemma tango (z:Positions (Key B G)): represent (tint G _ (stamp B G z)) = B.drape (fun i => G.lieExp ((tint G _ z) i)):=by
    funext i; obtain ⟨x,i⟩:=i; rw [represent_link]; by_cases he:(x,i)∈ B.trunks
    · rw [show B.drape _ _=1 from B.on_tree _ ⟨_,he⟩,show (tint G _ _ ) _=0 from ?_, G.mat_lieExp_zero]; ext k; change (stamp B G z ((x,coord i),k))=_; rw [ruler,dif_pos he];rfl
    let j:B.Free:=⟨(x,i),he⟩; rw [show B.drape _ _=G.lieExp _ from B.off_tree _ j]
    apply congr_arg; ext k; change stamp B G z ((x,coord i),k) = z (j,k); rw [ruler,dif_neg he]
end YM.MSbar.Rolling
