import YM.MS.Theater.BrightK
import YM.MS.Theater.Place

set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge} {h r:ℕ} {u:ℤ} {X:Law G} {B:Physical.Deck G}
abbrev Film0 (G:Gauge)(h r:ℕ): Submodule ℝ ( Pol G ):= ( Allowed G h r ).comap (( orbit G ).restrictScalars ℝ) ⊓ ( charge G ( h,r ) ).restrictScalars ℝ
lemma cinema (p:Pol G) : p∈ Film0 G h r ↔ At p (h,r) ∧ p∈ Labels.invariantSpace G ∧ Labels.conjPol p=p:= by refine ⟨ fun hp=> ⟨ hp.2,(Governed hp.2 ).mp hp.1⟩, fun ⟨ h,t⟩=> ⟨ (Governed h).mpr t, h ⟩ ⟩ -- args.F
lemma chooseX (hX:X∈Allowed G h r): ∃ p∈ Film0 G h r, orbit G p=X:= by
   obtain ⟨p,hp,rfl⟩:=shot ⟨ hX.1,hX.2.weight ⟩; exact ⟨p,⟨ hX,hp ⟩, rfl⟩
variable (G h r) in
abbrev stageM : Film0 G h r →ₗ[ℝ] WickPol G := (( reduceEq.toLinearMap ).restrictScalars ℝ) ∘ₗ ( Film0 G h r ).subtype
abbrev IvSpace (G:Gauge)(h r:ℕ): Submodule ℝ (WickPol G):= LinearMap.range (stageM G h r)
def over0 (G:Gauge)(h r:ℕ): Film0 G h r→ₗ[ℝ] Allowed G h r := ( ( ( orbit G ).restrictScalars ℝ) ∘ₗ ( Film0 G h r ).subtype ).codRestrict (Allowed G h r) (fun x=> x.property.1)
lemma f_standard (G:Gauge)(h r:ℕ): Bijective (over0 G h r):= by
    constructor; · intro f g he; exact Subtype.ext ( opaqueL ((cinema _).mp f.property|>.1) ((cinema _).mp g.property|>.1) ( congr_arg ( fun p:Allowed G h r=> p.val ) he ) )
    rintro ⟨x,hx⟩; obtain ⟨p,hp,rfl⟩:= chooseX hx; exact ⟨ ⟨p,hp⟩,rfl⟩
def craftK (G:Gauge)(h r:ℕ): ↥( Film0 G h r )≃ₗ[ℝ] Allowed G h r:= LinearEquiv.ofBijective _ ( f_standard G h r )
variable (B)
def Resume (h r:ℕ): B.carries ( h:ℤ ) r →ₗ[ℝ] Film0 G h r:= ( craftK G h r ).symm.toLinearMap ∘ₗ Submodule.inclusion B.le
lemma honor (x: B.carries h r): orbit G ( Resume ( G:=G ) B h r x ).val=x.val:= congr_arg (fun p:Allowed G h r=>p.val) ((craftK G h r).apply_symm_apply _)
local notation "Vκ"=> Resume B h r
variable (h r) in
def Staff: B.carries h r→ₗ[ℝ] IvSpace G h r:= ( stageM G h r ).rangeRestrict ∘ₗ Vκ
lemma no_self (x:B.carries h r) (he:Staff h r B x=0): x=0:= by
   have hn:x.val∈ Null G h r:= by rw [ ← honor B x ]; exact (certN ( ( Vκ x ).property.2 ) ( ( Vκ x ).property.1 ) ).mpr ( congr_arg ( fun v:IvSpace G h r=>v.val ) he )
   apply Subtype.ext; apply (Submodule.mem_bot ℝ).mp; have h':x.val∈ B.carries h r ⊓ Null G h r:=⟨x.property,hn⟩; rwa [(B.disjoint h r).eq_bot] at h'
lemma on_self (q:IvSpace G h r): ∃ x, Staff h r B x = q:= by
   obtain ⟨q,x,rfl⟩:= q; let V:=orbit G x.val; have hv: V∈ Allowed G h r:= x.property.1; rw [← B.sup] at hv; obtain ⟨f,hf,F,hF,he⟩:= Submodule.mem_sup.mp hv; let u:B.carries h r:= ⟨ f,hf⟩; refine ⟨ u,?_⟩; apply Subtype.ext; symm; apply sub_eq_zero.mp; change reduceEq x.val - reduceEq (Vκ u).val=_; rw [ ← map_sub ];
   let Q:= x.val - ( Vκ u ).val; have heQ : orbit G Q=F:= by unfold Q; rw [map_sub,honor B u, ← show f+F=orbit G x.val from he ]; unfold u; dsimp only; abel
   have hp:= ( ( x-Vκ u ): Film0 G h r ).property; apply (certN ( h:=h ) ( r:=r ) ( p:=Q ) ?_ ?_ ).mp; exact heQ.symm ▸ hF; exact hp.2; exact hp.1
def Studio (h r:ℕ): ↥( B.carries h r )≃ₗ[ℝ] IvSpace G h r:= LinearEquiv.ofBijective ( Staff h r B ) ⟨LinearMap.ker_eq_bot.mp ( eq_bot_iff.mpr ( fun x hx=> (Submodule.mem_bot _).mpr (no_self B x ( LinearMap.mem_ker.mp hx )) ) ),on_self B⟩
def film (i:B.BIndex h r): Pol G:= ( Vκ (( Module.finBasis ℝ (B.carries h r) ) i) ).val
lemma lamp_here (i:B.BIndex h r): orbit G ( film B i ( h:=h ) )=B.raw h r i:= honor B _ -- h inferred? binder h as Nat? local `notation` insert in def args.
lemma filmW (i:B.BIndex h r): film B i∈ Film0 G h r:= ( Vκ (( Module.finBasis ℝ (B.carries h r) ) i) ).property
lemma sees (i:B.BIndex h r): reduceEq (film B i (h:=h))=(Studio B h r ( Module.finBasis ℝ _ i )).val:= rfl
end YM.MS.Theater
