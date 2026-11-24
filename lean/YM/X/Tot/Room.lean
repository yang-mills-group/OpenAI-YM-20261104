import YM.X.Tot.Aroma
/-!
# Valuation + separation of the three outer nodes. Use after tagging, `Page(T,W)` with arbitrary W. Aperture-relocating Apt mark possibly at one pin. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {q:ℕ+}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}
local notation "fℕ"=>(atTop:Filter ℕ)
local notation "Q"=> (qu q G)
variable (x y z:Fielding.Walk)(T:Set ℕ)(W:Set (Marks G))(A B C': Foam G) -- name W earlier var
local notation "Θ"=> Page q T W
local notation "Ψ"=> Foam G
abbrev Lift (x:Fielding.Walk)(A:Foam G):Foam G:= fun i=> dress (x i) (A i)
local notation "U"=> id (α:=ℕ)
local notation "F"=> Fin 3
lemma at_mat (l:List (Stool G)): Lift x (textA q l)= thing (l.map (liftC q U x)):= by
     induction l with
     | nil=> simp only [List.map_nil,thing_one, Tot.empty]; funext k; exact map_one _
     | cons a l IH=>
       change Lift x (textA q (a::l))=_; rw [text_cons,List.map_cons,thing_cons]; funext i; change dress _ (credit q a i * _) =_ * _; rw [map_mul,gen, ←IH]; rfl
lemma carry (h:A∈ Page q T W): Carries q U x (Lift x A):= by
    induction h using Submodule.span_induction with
    | mem i hi=> obtain ⟨l,g,hp,_,_,rfl⟩:=hi; rw [show Lift x (g • textA q l)=charge g*Lift x (textA q l) from ?_, at_mat]; swap; · rw [unify];ext1 i; exact map_smul (dress _) _ _
                 let t:=l.map (liftC q U x); refine ⟨t.length,Bag.point _ (Bag.necklace t ?_ le_rfl) _ (rear id _ hp)⟩; intro i hi; obtain ⟨b,h,rfl⟩:=List.mem_map.mp hi; exact ⟨b,rfl⟩
    | zero=> refine ⟨0,?_⟩; rw [show Lift x (0:Foam G)=0 from funext (fun i=> map_zero (dress (x i)))]; exact Submodule.zero_mem _
    | add a b _ _ x₁ y=>unfold Lift;simp_rw [Pi.add_apply,map_add]; exact x₁.add U y -- field order
    | smul a p _ h=> obtain ⟨c,h⟩:=h; refine ⟨c,?_⟩; unfold Lift; simp_rw [Pi.smul_apply,map_smul]; exact Submodule.smul_mem _ a h
lemma tri_tilt (A B C:Curly G)(z:Cover): tri (flow G n) (dress z A) (dress z B) (dress z C)=tri (flow G n) A B C:= Eq.symm (triple_sym (flow G n) A B C (pointB z) (flow G n) (Fund.tilt z|>.symm)) -- grammar notation
lemma illA {A:Foam G}(h: A∈ Page q T W)(hq:1<q.val) (hr: r>0): Plate.Apt q r A:= by
    -- x ignored. priced on ALL Tide. prove via visa+Tide evaluation
    induction h using Submodule.span_induction with
    | mem i hp=>
       obtain ⟨l,g,h,hX,hY,rfl⟩:=hp; clear hX hY; refine Plate.Apt.up (?_ : Plate.Apt q r (textA q l)) _ h; -- show along Tide∗ calculate
       refine ⟨⟨l.length,fun i=>by rw [←leafy.mp (echelon q l i)]; exact Heat.Top.cut_bound l.length _⟩,fun P hp=>?_⟩; induction l with
       | nil=> simp_rw [Tot.empty,Pi.one_apply,map_one]; exact constell 1
       | cons a l IH=> simp_rw [text_cons,Pi.mul_apply,map_mul]; apply breaths _ IH; simp_rw [credit,carbon,normF,flatL, map_smul]; apply Released.lin Complex.ofRealCLM.toLinearMap; have he:= hp.later a.k a.x a.order 0 (by rw [norm_zero]; exact hr.le) (fun _:ℕ=>0) (plot.constant hq 0); simp_rw [leads_zero] at he; exact he
    | zero=> refine ⟨⟨0,fun i=> Plate.duty.zero⟩, fun m h=>?_⟩; simp only [Pi.zero_apply,map_zero]; exact Released.zero
    | add a c _ _ x y=> exact x.add y
    | smul a m _ h=> exact h.up (fun _=> a) (constell a) -- defeq
variable (h:Geom q r x y z)(hr:r>0)(hq:1<q.val) {T₁ T₂ T₃:Set ℕ}{B₁ B₂ B₃:Set (Marks G)}
lemma tri_link (Qv:Symmetric V)(a b c:Normal.poly V): tri Qv a b c= spine Qv ![b,c] Finset.univ a:= by
    rw [tri,market]; unfold spine spiro; rw [Fin.prod_univ_two,blend_components]; simp only [pure,one_mul,Matrix.cons_val_zero,Matrix.cons_val_one]; rw [mul_assoc]
include h hr hq
lemma g_cost (A₀:Plate.Apt q r A)(hb:B∈ Page q T₂ B₂)(hc:C'∈ Page q T₃ B₃): Released (gather q x y z A B C'):= by
    obtain ⟨g,hg,hx⟩:= h.reach q x y z; let Y:=y-x; let Z:=z-x; let T: Fin 2→Fielding.Walk:= ![Y,Z]; let p(_:Unit)(j:Fin 2):=g (Fin.succ j)-g 0; let q':= qu q G
    have he : gather q x y z A B C'= Crate.lap (Finset.univ (α:=Fin 2)) q' ![Lift Y B,Lift Z C'] A:= by
        ext1 k; unfold gather; rw [show y k=x k+Y k from ?_, show z k=x k + Z k from ?_,← dress_addT,←dress_addT,tri_tilt,tri_link];
        · unfold Crate.lap drip; apply congr_arg (fun p:Fin 2→Curly G=> spine (qu q G k) p Finset.univ (A k)); ext1 i; fin_cases i <;> rfl
        · unfold Z;simp
        unfold Y;simp
    rw [he]; have hs(j:Fin 2):plot q (T j) (p () j):= by fin_cases j; exact plot.sub (hx 1) (hx 0); exact plot.sub (hx 2) (hx 0)
    refine Rays.near_lap hq Finset.univ T (p ()) (fun i _=>hs i) ?_ hr.le ?_ ?_ A₀; · intro i _ j _ h'; by_contra ht; have hh:0 < ‖g i.succ-g j.succ‖:= hr.trans (hg i.succ (by simp) j.succ (by simp) (Fin.succ_injective .. |>.ne ht)); unfold p at h'; rw [sub_left_inj] at h'; simp [h'] at hh
    · intro i _; exact hg i.succ (by simp) 0 (by simp) (by simp)
    intro i _; fin_cases i; exact carry Y T₂ B₂ B hb ; exact carry Z T₃ B₃ C' hc
end YM.PositionX.Tot
