import YM.MS.Tone.Timbre

/-!
# Fourier frequencies near the zone

Density for translated identities. Define the evaluation on the unlopped mesh,
 lifted momenta permissible any reciprocal shift. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone.Mesh
open Function Filter Set Finset Plane Koszul Cylinder Lab Lattice Native Bare Focus Landau Momentum Paint Color Orient
open scoped Topology ContDiff
open Real
variable {G:Gauge}
local notation "W" => Dot G Cover
local notation "E" => LightMode G Cover
local notation "B" => Branch G Axis
local notation "V" => LightMode G QP

variable (F:W) (n:Side)
def hz (n:Side): Cover→+ QP:={
   toFun x:= (n.val:ℝ)⁻¹ • rep x
   map_zero':=by simp
   map_add' x y:=by simp [smul_add] }
abbrev proper (n:Side): Set QP:= range (hz n)
lemma position (x:Cover): (n.val:ℝ) • hz n x=rep x:= by change (n.val:ℝ) • ((n.val:ℝ)⁻¹ • rep x)=_; rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast n.property.ne'),one_smul]
lemma dual (p q:QP)(t:ℝ): bill p (t • q)=bill (t • p) q:= by
   unfold bill pairing; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,mul_left_comm t]
lemma plink (v:V)(hv:v.2∈proper n)(x y:Cover)(H:wrap n x=wrap n y):
    paywave v (v.1,x) = paywave v (v.1,y):= by
    rcases v with ⟨i,p⟩; obtain ⟨b,rfl⟩:= hv; obtain ⟨z,rfl⟩:= Bloch.cover_of_eq x y H; simp only [pw,emb_add,rightadd];
    have hz' : embed (n.val • z)=(n.val:ℝ) • embed z:= by ext; simp [embed]
    rw [hz',dual,position,reciprocal,mul_one]
def hint (p:V)(x:LightMode G (Site n)):= paywave p (x.1, Lattice.lift x.2)
lemma bridge (v:V)(h:v.2∈proper n)(x:E): hint n v (post (wrap n) x)= paywave v x:= by
    rcases x with ⟨a,x⟩; by_cases he:a=v.1
    · subst a; exact plink n v h (Lattice.lift (wrap n x)) x (wrap_lift _)
    simp [hint,paywave,need id (j:=v.1) (i:=a) (Ne.symm he),post] -- name check
lemma equal_sh {A Dx R:Type}[CommRing R](F:Cyl A R)(K U:Dx→A→R)(l:List Dx)(h:∀ i∈l,K i=U i): shade K F l=shade U F l:= by
    induction l generalizing F with
    | nil=> simp
    | cons i l ih=> obtain ⟨s,hs⟩:=fromCyl F; rw [deriv_lum K _ _ hs,deriv_lum U i _ hs]; apply Finset.sum_congr rfl; intro j _; rw [h i (by simp), ih (enter j F) fun k hk=> h k (List.mem_cons_of_mem _ hk)]
lemma project (F:Dot G Cover) (n:Side) (l:List (LightMode G QP))(h:∀ i∈l,i.2∈proper n): shade (hint n) (shown n F) l=run F l:= by
    unfold shown transport; rw [study]; exact equal_sh F _ _ l (fun i hi=> funext (bridge n i (h i hi)))
lemma consents (F:Dot G Cover)(n:Side) (l:List V)(hh:∀ i∈l,i.2∈proper n)(h:net l=0): shade (hint n) (sumHome (shown n F)) l=(n.val:ℂ)^4 * run F l:= by
    rw [total_uses,map_sum,Finset.sum_apply];
    have he (t: Site n) : Lab.Shift t (shown n F)=shown n (Lab.Shift (Lattice.lift t) F):= by rw [show shown n _= _ from trans_shift F _ (wrap n),wrap_lift]; rfl
    simp_rw [he,project _ n _ hh,movement,h,pay0]; simp

lemma idle (p:QP): ∃ x:∀ _:Side,QP, (∀ n,x n∈proper n) ∧ Tendsto x atTop (𝓝 p):= by
    let d (n: Side) : ℝ:=2*π / n.val
    have hp (n:Side) : 0<d n:= div_pos (by positivity) (Bloch.side_pos _)
    let u (n:Side)(i:Axis) := ⌊p i/d n⌋
    let x (n:Side) := hz n (u n)
    have hs : Tendsto (fun n:Side=>(n.val:ℝ)) atTop atTop:= by
       refine tendsto_natCast_atTop_atTop.comp ?_; refine tendsto_atTop.mpr (fun n=>?_); exact (eventually_ge_atTop (α:=Side) (⟨n+1,by omega⟩ : Side)).mono (fun i hi=> le_trans (by omega : n≤n+1) hi) -- PNat.mk inspect
    have H: Tendsto d atTop (𝓝 0) := by unfold d; simp_rw [div_eq_mul_inv]; simpa using (tendsto_const_nhds (x:=2*π)).mul (tendsto_inv_atTop_zero.comp hs)
    refine ⟨x,fun n=>⟨_,rfl⟩,tendsto_pi_nhds.mpr fun i=> ?_⟩
    have hv (n:Side) : x n i=d n * (u n i:ℝ):= by unfold x hz; change (n.val:ℝ)⁻¹ * (2*π*(u n i:ℝ))=_; unfold d; ring
    simp_rw [hv]; refine tendsto_of_tendsto_of_tendsto_of_le_of_le (show Tendsto (fun n=>p i-d n) _ _ from ?_) (tendsto_const_nhds (x:=p i)) ?_ ?_
    · simpa using (tendsto_const_nhds (x:=p i)).sub H
    · intro n; have hh:= (div_lt_iff₀ (hp n)).mp (Int.lt_floor_add_one (p i/d n)); change p i - d n ≤ d n * ↑(Int.floor (p i/d n)); linarith
    intro n; dsimp only; rw [mul_comm]; exact (le_div_iff₀ (hp n)).mp (Int.floor_le _)
end YM.MS.Tone.Mesh
