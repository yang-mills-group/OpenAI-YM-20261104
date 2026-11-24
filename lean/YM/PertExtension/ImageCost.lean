import YM.PertExtension.WindowKernel

/-! Summation on the frequency grid at distant image arguments. This step is
before taking Maxwell or spacing limits. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace YM.PertExtension.LatticePT.Band
open MeasureTheory Measure Filter Maxwell Topology Analysis Next Next.Rank Next.Rank.Perch Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Prayer
open Function Finset ZMod
open scoped ContDiff Topology BigOperators Classical NNReal FourierTransform RealInnerProductSpace
local notation "ℑ" => Complex.I
variable {G : Gauge}(n:Side)(i:Axis)(z:E4)

def sizeInv (n:Side):= (n.val:ℝ)⁻¹
lemma size_pos : 0<sizeInv n:= Next.Rank.Radian.positive n

lemma sizeInv_le:sizeInv n≤1:=inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr n.pos)

def pebble:= addr n (step i)
lemma mapzero :mapZ 0=0:= by ext i;change (((0:ℤ)):ℝ)=0;exact Int.cast_zero
lemma peb_step : pebble n i=sizeInv n • basis i:= by unfold pebble addr;rw [show mapZ (step i)=basis i from by simpa only [mapzero,zero_add] using mapZ_step 0 i];rfl
lemma peb_norm : ‖pebble n i‖=sizeInv n:= by rw [peb_step,norm_smul,sizeInv,Real.norm_of_nonneg (by positivity),basis_norm,mul_one]
lemma addr_step (x:Cover) : addr n (x+step i)=addr n x + pebble n i:= by rw [peb_step,addr, mapZ_step, smul_add];rfl

def banded (F:E4→ℂ)(z q:E4) := wave z q*F q
lemma wave_second_add x y : wave z (x+y)=wave z x *wave z y:=by rw [terrel,terrel,terrel]; unfold chimes;rw [inner_add_left,Complex.ofReal_add,mul_add,Complex.exp_add]

lemma scan_sub (F H:E4→ℂ)(d): scansP n (F-H) d=scansP n F d-scansP n H d:=by unfold scansP;rw [← smul_sub, ← Finset.sum_sub_distrib];rfl
lemma scan_scale (r:ℂ)(F:E4→ℂ)(d): scansP n (fun z=>r*F z) d=r*scansP n F d :=by unfold scansP; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; simp_rw [smul_eq_mul,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>by ring


-- Use compact restriction at 2 and one extra box while shifting frequency labels
variable {F:E4→ℂ}(h:eventP 2 F)
include h
lemma extend : scansP n F 2=scansP n F 3:= by
   have ht: eventP 3 F:=fun x hx=>h x (by apply lt_trans _ hx;norm_num)
   rw [(grid_born n F 2 h).2.symm,(grid_born n F 3 ht).2.symm]
lemma shift_bag : let W (x:Cover):=F (addr n x)
    (∑ x∈room n 3,W (x+step i))=∑ x∈room n 3,W x :=by
    intro W
    let S:=room n 3;let E:= S∩S.image (fun x=>x+step i)
    have H : S∩(S.image (fun x=>x+step i))⊆ S.image (fun x=> x+step i):= Finset.inter_subset_right
    have ht : ∀ x : Cover, x∉E → W x=0 :=by
      intro x he; by_contra hx
      have hp : ‖addr n x‖ ≤ 2:= le_of_not_gt (fun h' => hx (h (addr n x) (by exact_mod_cast h')))
      have hb:addr n (x-step i)+pebble n i=addr n x:= (addr_step n i (x-step i)).symm.trans (by rw [sub_add_cancel])
      have hr: ‖addr n (x-step i)‖≤(3:ℕ) :=by
           rw [← sub_eq_of_eq_add (Eq.symm hb)] -- adjust opposite
           apply (norm_sub_le ..).trans
           rw [peb_norm]; exact_mod_cast show ‖addr n x‖+sizeInv n≤(3:ℝ) from by linarith only [hp, sizeInv_le n]
      apply he;apply Finset.mem_inter.mpr; refine ⟨addressBW _ _ (hp.trans (by norm_num)), (Finset.mem_image.mpr ⟨x-step i,addressBW _ _ hr,sub_add_cancel x (step i)⟩)⟩ -- placeholders
    calc
     _ = ∑ x∈ S.image (fun x=> x+step i), W x := (Finset.sum_image ((show Injective (fun x:Cover=>x+step i) from fun a b h=>add_right_cancel h).injOn)).symm
     _ = _:= by exact (Finset.sum_subset H (fun x _=>ht x)).symm.trans (Finset.sum_subset Finset.inter_subset_left (fun x _=>ht x))

def shiftF (n : Side)(i : Axis)(F : E4→ℂ) := fun q=> F (q+pebble n i)
def bandShift := fun q=>banded F z (q+pebble n i)
lemma shifted_event : eventP 3 (shiftF n i (F:=F)):= by
  intro x hx; apply h
  have he: ‖x‖≤ ‖x+pebble n i‖+ sizeInv n:= by
     rw (occs:=.pos [1]) [show x=x+pebble n i-pebble n i by rw [add_sub_cancel_right]]
     convert! norm_sub_le ..; exact (peb_norm n i).symm
  change (2:ℝ) < _
  have hh:(3:ℝ)< ‖x‖:=hx; linarith only [he,hh,sizeInv_le n]
lemma shifted_sum :scansP n (bandShift n i z (F:=F)) 3=scansP n (banded F z) 3:= by
    have H (k:ℕ)(hh:eventP k F):eventP k (banded F z) := fun q h=> by rw [banded,hh q h,mul_zero] -- remove show
    unfold scansP
    simp_rw [bandShift,← addr_step n i]
    apply congr_arg
    exact shift_bag n i (H _ h)

def cwave :=wave z (pebble n i)
lemma doubled : (cwave n i z-1)*scansP n (banded F z) 3 = (cwave n i z)* scansP n (banded (F-shiftF n i (F:=F)) z) 3 := by
    let p:=3
    let A:= scansP n (banded F z) 3
    let B:= scansP n (banded (shiftF n i (F:=F)) z) 3
    let q:= cwave n i z
    have H:A=q*B:=by unfold A B; rw [← scan_scale n q];exact (shifted_sum n i z h).symm.trans (congr_arg (fun T=>scansP n T 3) (funext fun v=>by unfold q bandShift banded shiftF cwave;rw [wave_second_add];ring))
    let D:= scansP n (banded (F-shiftF n i (F:=F)) z) p
    have h:D=A-B:= by unfold D A B p; rw [← scan_sub]; congr 1;ext1 v; apply mul_sub
    change (q-1)*A=q*D;rw [show (q-1)*A = q*A-A from by ring];nth_rw 2 [H]; rw [h];ring
lemma grid_integrable (f:E4→ℂ)(R:ℕ)(hx:eventP R f): Integrable fun q=>f (addr n (mark n q)):= (grid_born n f R hx).1
omit h -- section include warning

end YM.PertExtension.LatticePT.Band
namespace YM.PertExtension.LatticePT.Band
open MeasureTheory Measure Filter Maxwell Topology Analysis Next Next.Rank Next.Rank.Perch Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Prayer
open Function Finset ZMod
open scoped ContDiff Topology BigOperators Classical NNReal FourierTransform RealInnerProductSpace
local notation "ℑ" => Complex.I
variable {F : E4→ℂ}{C : ℝ}

def meter : ℝ:= Maxwell.normal⁻¹ * Real.exp ((8:ℝ)^2) * 8
-- warning exp(8)^2 vs exp(8^2) notation: in Lean (-‖x‖^2) works, here need (exp (8^2)).
def halo (g:E4→E4):Prop:= ∀ x,‖g x-x‖≤5
lemma walk_pointwise {F:E4→ℂ}(H:Lip F 2 C)(hC:0≤C){s:ℝ}(hs:s>0)(hh:s≤1) {x z:E4}(hx:x∈away)(hz:‖z-x‖≤5*s):
   ‖F x-F z‖ ≤ (meter*20*C*s)* ‖liturgy 1 x‖:=by
  have hm:0≤meter:=by unfold meter;have he:= Maxwell.normal_pos;positivity
  by_cases h:‖x‖ ≤ 8
  · have hZ := skin H hC _ _ _ (mul_pos (by norm_num) hs) hz hx
    have hF:=fern x (show (0:ℝ)<8 by norm_num) (norm_pos_iff.mpr hx) h
    change _≤meter*_ at hF
    calc
     _ ≤ 20*C*s*‖x‖⁻¹ := hZ.trans_eq (by ring)
     _ ≤ _:= le_trans (mul_le_mul_of_nonneg_left hF (by positivity)) (le_of_eq (by ring))
  have ht:8<‖x‖:=lt_of_not_ge h
  have hv := norm_sub_norm_le x z; rw [norm_sub_rev x z] at hv
  have hh: (2:ℝ)< ‖z‖:= by linarith only [ht,hv,hz,hh]
  rw [H.event x (by exact_mod_cast (lt_trans (by norm_num) ht : (2:ℝ)<‖x‖)),H.event _ (by exact_mod_cast hh),zero_sub,norm_neg,norm_zero]
  positivity

def costImage : ℝ := 40 * meter * (∫ t:E4, ‖liturgy 1 t‖)
lemma wave_cost (n:Side)(i:Axis)(w:E4)(H:Lip F 2 C)(hC:0≤C):
   ‖cwave n i w -1‖ * ‖scansP n (banded F w) 3‖ ≤ costImage*C / n.val:= by
   let d:=pebble n i; let Y:=banded (F-shiftF n i F) w
   let s:=sizeInv n; let B (x:E4):=2 * ((meter*20*C*s)* ‖liturgy 1 x‖)
   let g x:=addr n (mark n x); let L x:=Y (g x)
   have hg x: ‖g x-x‖≤5*s:= by have h:=rock (c:=n) (u:=x);rw [dist_eq_norm] at h;change _ ≤ 5*(n.val:ℝ)⁻¹; exact h.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
   have hg' x: ‖(g x+d)-x‖≤5*s:= by have h:=rock (c:=n) (u:=x); rw [dist_eq_norm] at h; rw [show g x+d-x=(g x-x)+d by abel]; refine (norm_add_le ..).trans ((add_le_add h (le_of_eq (peb_norm n i))).trans_eq ?_); unfold s sizeInv;ring
   have hp (x:E4)(hx:x∈away): ‖L x‖ ≤ B x := by
      unfold L Y banded;rw [norm_mul,price_wave,one_mul];unfold shiftF;change ‖F (g x) - F (g x+d)‖≤_
      have hz := walk_pointwise H hC (size_pos n) (sizeInv_le n) hx (hg x)
      have hy:= walk_pointwise H hC (size_pos n) (sizeInv_le n) hx (hg' x)
      unfold B;rw [two_mul,show F (g x)-F (g x+d)=(F (g x)-F x)+(F x-F (g x+d)) by abel]
      exact (norm_add_le ..).trans (add_le_add (by rw [norm_sub_rev]; exact hz) hy)
   have hF:eventP 3 F:= fun x h=>H.event x (lt_trans (by norm_num) h)
   have he:eventP 3 Y:=fun z hz=> by rw [show Y z=0 from ?_]; unfold Y banded; rw [Pi.sub_apply,hF _ hz,(shifted_event n i H.event) _ hz,sub_self,mul_zero]
   obtain ⟨hfin,hE⟩:=grid_born n Y 3 he
   have Ht: Integrable (fun z:E4=>‖liturgy 1 z‖) := (liturgy_int (by norm_num : (0:ℝ)<1)).norm
   have hb:Integrable B:= (Ht.const_mul _).const_mul _
   have HH:= hp
   calc
    _ = ‖scansP n Y 3‖:= by rw [← norm_mul,doubled n i w H.event,norm_mul,cwave,price_wave,one_mul]
    _ ≤ ∫ t:E4, ‖L t‖:= by rw [←hE]; exact norm_integral_le_integral_norm ..
    _ ≤ ∫ t:E4, B t:=integral_mono_ae hfin.norm hb (lit_ae.mono fun x hx=>hp x hx)
    _ = _ := by unfold B costImage;rw [integral_const_mul,integral_const_mul,div_eq_mul_inv]; unfold s sizeInv;ring
end YM.PertExtension.LatticePT.Band
