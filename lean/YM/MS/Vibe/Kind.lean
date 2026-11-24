import YM.MS.Vibe.Scale
/-!
# Weak requirements for master shapes
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Emit
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F: T (Flats G)}{J N L:Flats G}{f:Coat G}{b c:Bool}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ}
structure Host (X:Flats G)(h:ℕ): Prop where
   cap : ∃ r, Cap r X
   bill: Moony false X
   tall: Stay h X
namespace Host
lemma zero (G:Gauge)(h:ℕ) : Host (0:Flats G) h:= ⟨ ⟨0,fun _=> (washed _).zero⟩,fun _=> Sun.zero, fun y s=> by rw [pageZ]; exact Live.zero⟩ -- unused i
lemma plus (h :Host J n)(hp:Host L n): Host (J+L) n:= by obtain ⟨⟨r,hF⟩,ht,hx⟩:=h; obtain ⟨⟨s,h'⟩,hp,H⟩:=hp; exact ⟨ ⟨ max r s, (washed _).plus (Cap.rise hF (le_max_left ..)) (Cap.rise h' (le_max_right ..))⟩, Sun.HeapS.plus ht hp, Stay_add hx H⟩
lemma smul (h:Host J n)(c:ℂ): Host (c • J) n:= by obtain ⟨⟨r,hF⟩,ht,hx⟩:=h; exact ⟨ ⟨r, fun i=>(hF i).mono fun _ hu=> (grade _ G).smul_mem _ hu⟩,fun _=> Sun.smul (ht _) _, Stay_scale hx _ ⟩
lemma sum (S:Finset I){X:I→ Flats G}(hp:∀ i∈S,Host (X i) h): Host (∑ i∈S,X i) h:= by classical induction S using Finset.induction with| empty=> rw [Finset.sum_empty]; exact zero ..| insert i s hi ih=> rw [Finset.sum_insert hi]; exact (hp i (by simp)).plus (ih fun j hj=>hp j (Finset.mem_insert_of_mem hj))
lemma tree {x:ℂ}{L:Rip G}(hp:Host J n)(hr:Host N m)(he:reverseF L)(hL:Knot false L)(hy:closedF L c)(ha:x-n-m=-(h:ℂ)): Host (TreeN L J N) h:= by obtain ⟨⟨r,H⟩,hM,hS⟩:=hp; obtain ⟨⟨r',H'⟩,hM',hY⟩:=hr; exact ⟨⟨ r+r'-2, capA H H' he⟩,Moony.tree hM hM' hL he hy,StayB ha hL he hS hY⟩
lemma core (hp:Host J n): Host (step0 G J) n:= by obtain ⟨⟨r,H⟩,hM,hS⟩:=hp; exact ⟨⟨r-2,capC _ H hM (c_bo 0)⟩,Moony.cycle hM (c_bo 0),Cit hS hM (c_bo 0) (a:=4) (by ring)⟩
lemma prior (hp:Host J n): Host (QN G J) (n+1):= ⟨ let ⟨r,H⟩:=hp.cap;⟨ r,cap_QN H⟩, Moony.tap hp.bill,Stay_Q _ hp.tall⟩
lemma brake (hp:Host J n): Host (CycleN ( B0 G 0) J) (n+1):= by
    let U:= B0 G 0; have hv := (B_caps G 0).clearer; obtain ⟨⟨r,H⟩,hM,hS⟩:=hp; exact ⟨⟨ r-2, capC _ H hM hv⟩, Moony.cycle hM hv,Cit hS hM hv (a:=3) (by push_cast; ring) ⟩
lemma Pose_p (hX: ∀ i,Host (X i) 4)(hf:∀ i,Host (F i) h)(n:ℕ)(t:ℂ) : Host (Pose n t X F) (h+1):= by
    unfold Pose park; rw [ LinearMap.add_apply, paired]; refine ((hf _).prior.plus (hf _).brake).plus (( Host.sum _ (fun i hi=>?_)).smul _); exact Host.tree (hX _) (hf _) ( reverse_b G 0) ( B_caps G 0|>.clearer) (cl_b G 0) (x:=3) (by push_cast; ring)
lemma host (hv:Gang b h t J): Host J h:= by obtain ⟨r,hr⟩:= hv.price; exact ⟨ ⟨r,clockCap hr⟩, all0 (clockMoon hr), hv.dost ⟩ -- h shadows
end Host
end YM.MS.Emit
