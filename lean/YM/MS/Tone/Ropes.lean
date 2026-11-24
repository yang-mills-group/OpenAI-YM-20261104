import YM.MS.Tone.CurlsPlane

/-! The anti/ghost rank two and `cstar` rank three.

 Left sign. Include orientation charges with p at first entry. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone.Frame
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}
local notation "B"=>Branch G Axis
local notation "Y" => Dot G Cover
local notation "pC"=> field (Landau.parity (A:=Axis) (C:=G.ColorIndex)) (P:=QP)
local notation "w0"=> List (LightMode G QP)

lemma logo0 (i:LightMode G Cover): run (Cylinder.single i) []=0:= by simp [run,Cylinder.single,Cylinder.atLetter]
lemma small (p:LightMode G QP) (F:Y)(H:Y)(h:run F []=0): run (couple DotFlip F H) [p]=run F [p]*run H []:= by rw [wave_cost,D_eval p (product _ _ _),D_product]; simp [h]
lemma roles (a b:LightMode G QP)(F H:Y) (h:run F []=0)(he:run H []=0): run (couple DotFlip F H) [a,b]=run F [a]*run H [b]+ cross (pC a) (pC b)*run F [b]*run H [a]:= by
    rw [wave_cost,D_eval a (product _ _ _),D_product]; simp only [Pi.add_apply]; simp_rw [show ∀ f h:Row B QP ℂ, product pC f h [b]=f [b]*h []+f []*h [b] from fun f h=> by rw [D_eval b (product _ _ _), D_product]; simp]; -- inspect the order from signs ok
    simp [h,he,DotFlip]
lemma tip_ste (t:Cover)(i:Conn G)(q:Edge Cover)(p:LightMode G QP)(J:Conn G→Maurer.Ends G): run (steerA t i q J) [p]= ∑ j:Conn G, paywave p ((ghost,j),t) * (vel (J j) i (0:G.Color):ℂ) := by
    simp_rw [steerA,map_sum, Finset.sum_apply,small p (GH _ t) _ (logo0 ..)]; exact Finset.sum_congr rfl fun i hi=> (by rw [show run (GH i t) [p]= _ from pulse p (ghostAt i t)]; rfl)
lemma right_tag (j: Conn G)(p: LightMode G QP)(i: Axis): run (throat idRail (0,i) j) [p]=paywave p ((ghost,j),step i)-paywave p ((ghost,j),0):=by
    rw [throat,map_add,Pi.add_apply,tip_ste,tip_ste]; simp_rw [vel,Maurer.volt_zero,leftStem,rightStem,sub_zero,zero_sub];
    simp [baseC,PiLp.single_apply,apply_ite,endRail,idRail]; ring

lemma lowAng (i:Conn G)(x:Edge Cover): run (throat idRail x i) []=0:= by simp [throat,steerA,wave_cost,logo0,GH]
lemma cog_dim (x:Cover)(i:Conn G) : run (cog x i) []=0 ∧ ∀ k:LightMode G QP, run (cog x i) [k]=0:= by
    unfold cog; simp_rw [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply]; simp_rw [small _ (GH _ _) _ (logo0 ..),wave_cost,nil_product]; simp [GH,logo0]
-- legislative sign equation
lemma rope_pair (p q: LightMode G QP): run (ropes G idRail (0:Cover)) [p,q]=∑ i:Axis,∑ j:Conn G, (paywave p ((anti i,j),0)*(paywave q ((ghost,j),step i)-paywave q ((ghost,j),0))+cross (pC p) (pC q)*paywave q ((anti i,j),0)*(paywave p ((ghost,j),step i)-paywave p ((ghost,j),0))) := by
    unfold ropes; simp_rw [map_sub,map_sum,Pi.sub_apply, Finset.sum_apply,roles p q (AHplus _ _) _ (logo0 ..) (lowAng ..),roles p q (GHplus _ _) _ (logo0 ..) (cog_dim ..).1]; simp_rw [(cog_dim ..).2 p,(cog_dim ..).2 q,mul_zero,add_zero,Finset.sum_const_zero,sub_zero]; simp_rw [right_tag,AHplus,pulse]
-- collapse mixed S frame. p∈ ℝ. anti-c sign.
def μ2 (p:QP) (a b : Atom Axis) : ℂ:= match a,b with| (none,false),(some j,true)| (some j,true),(none,false) => -(I*wave p j)|_,_=>0
lemma triangle (i:Axis)(p:QP) : bill p (z i)*(bill (-p) (embed (step i))-1)= -(I*wave p i):= by
    rw [← s_wave p i,mul_sub,mul_one,opp,← inverse,centr,← rightadd]; rw [show z i+ -(z i+z i)= -z i by abel]; ring
lemma mantra (p:QP)(a b:Atom Axis)(i j:Conn G): run (ropes G idRail (0:Cover)) [((a,i),p),((b,j),-p)]= matchA i j (μ2 p a b):= by
    rw [rope_pair]; unfold paywave way; simp only [bornv,anti,ghost]; rcases a with ⟨_|a,_|_⟩ <;> rcases b with ⟨_|b,_|_⟩ <;> simp [matchA,μ2, ite_mul,mul_ite]
    · rw [Finset.sum_eq_single b,Finset.sum_eq_single j];
      · simp_rw [show pC (((none,false),i),p)=true from rfl, show pC (((some b,true),j),-p)=true from rfl,cross_true, show embed 0=(0:QP) from funext fun _=>Int.cast_zero,zero_add]; by_cases he:i=j; swap; · simp [he]
        simp only [he, if_true, and_self, right0]; have hh := triangle b (-p); rw [wave_neg,neg_neg,z] at hh; simp_rw [one_div,Pi.neg_apply,Complex.ofReal_neg] at hh; linear_combination (norm:=ring_nf) - hh
      · intro k _ he; simp [Ne.symm he]
      · simp
      · intro k _ he; simp [Ne.symm he]
      simp
    rw [Finset.sum_eq_single a,Finset.sum_eq_single i];
    · rw [show embed 0=(0:QP) from funext fun _=>Int.cast_zero]; by_cases he:i=j; swap; · simp [he,Ne.symm he]
      simpa [he,z] using triangle a p
    · intro k _ he; simp [Ne.symm he]
    · simp
    · intro k _ he; simp [Ne.symm he]
    simp
end YM.MS.Tone.Frame
