import YM.MS.Class.Cube
/-!
# The remaining rank-three vector-only term is fixed by antifield data

At momentum degree ≤1, transversality forces it to be zero. No distributions
 off momentum chart (all charts polynomial by the grade convention already).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau.Detect.Mark
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor
open scoped Topology ContDiff
open Complex (I)
variable {G: Gauge} {F : Law G} {h : ℤ}

abbrev steer (F:Law G) (i j k:CI G) (a b c:Axis) (p:FourP×FourP):= F [W a i p.1,W b j p.2,W c k (-(p.1+p.2))]
variable (X: Class F h) (H : ∀ i j k, token F i j k=0) (hv:h≤4)
include X
lemma steer_shape i j k a b c : Shape (steer F i j k a b c) (h-3):= by
   let I:= ContinuousLinearMap.fst ℝ FourP FourP; let J:=ContinuousLinearMap.snd ℝ FourP FourP
   let Q : Wire (Branch G Axis) (FourP×FourP) FourP := [((gauge a,i),I),((gauge b,j),J),((gauge c,k),-(I+J))]
   convert X.graded (FourP×FourP) Q (fun _=>by simp [Q,net]) using 1 <;> rfl
lemma steer_swap i j k a b c p q: steer F i j k a b c (p,q) = steer F j i k b a c (q,p):= by
   have hp:= X.swap [] (W a i p) (W b j q) [W c k (-(p+q))] (by simp [W,qnote,net])
   simpa only [List.nil_append,show cross (parity (W a i p).1) (parity (W b j q).1)=(1:ℂ) from rfl,one_mul,steer,add_comm q p] using hp
-- Sym of vanishing terms on any chart allows arbitrary permutation; we'll use this for classifying all legs.
lemma Class_zero {l k : List (Lane4 G)} (hw: l.Perm k) (hZ:net l=0) (hz:F k=0): F l=0:= by
   suffices hp : ∀ o : List (Lane4 G), net (o++l)=0 → F (o++k)=0 → F (o++l)=0 from hp [] hZ hz
   clear hZ hz; induction hw with
   | nil=> exact fun _ _ h=>h
   | cons x h ih=> exact fun o he hz=> by simpa using ih (o++[x]) (by simpa using he) (by simpa using hz)
   | swap x y l=> exact fun o he hz=>by rw [X.swap o y x l he,hz,mul_zero]
   | trans h H hz hu=>
       intro o he hp; exact hz o he (hu o (Eq.trans (((h.append_left o).map Prod.snd).sum_eq).symm he) hp)
include H hv
lemma ping_zero i j k a b p q r (hl : net [U a i p,W b j q,C k r]=0): F [U a i p,W b j q,C k r]=0:= by
   rw [anti_constant X hv _ _ _ _ _ _ _ _ (by simpa [U,W,C,qnote,net] using hl),changes X hv]; simp [H]
lemma steer_trans i j k b c p q: ∑ a:Axis,((p:FourP) a:ℂ)*steer F i j k a b c (p,q)=0:= by
   let r:= -(p+q); have ht:= X.closed [C i p, W b j q,W c k r] (by simp [C,W,qnote,net,r])
   have hz a:F [C i p,U a j q,W c k r]=0:= Class_zero X ((List.Perm.swap ..).trans ((List.Perm.swap ..).cons _)) (by simp [net,C,U,W,qnote,r]) (ping_zero X H hv j k i a c q r p (by simp [U,W,C,qnote,r,net]))
   have he a:F [C i p,W b j q,U a k r]=0:= Class_zero X (((List.Perm.swap ..).trans ((List.Perm.swap ..).cons _)).trans (List.Perm.swap ..)) (by simp [net,C,U,W,qnote,r]) (ping_zero X H hv k j i a b r q p (by simp [U,W,C,qnote,r,net]; abel))
   rw [qGhost,qAA,qAA,q0] at ht; simp_rw [at_D,hz,he,mul_zero,Finset.sum_const_zero,add_zero,sub_zero,mul_assoc,← Finset.mul_sum] at ht; exact (mul_eq_zero.mp ht).resolve_left Complex.I_ne_zero
lemma steer_origin i j k a b c p: steer F i j k a b c (0,p)=0:= by
   let f:=steer F i j k a b c; let T:= fun t:ℝ=> (t • spike a,p)
   have hz : f ∘ T =ᶠ[𝓝[≠] 0] 0:= by
      filter_upwards [self_mem_nhdsWithin] with t ht; have ht:t≠0:= by simpa using ht
      have h:= steer_trans X H hv i j k b c (t • spike a) p
      rw [Finset.sum_eq_single a (fun j _ he=>by simp [he]) (by simp)] at h; simpa [f,T,Function.comp_def,ht] using h
   have hq := (steer_shape X i j k a b c).smooth.continuous.comp (by unfold T; fun_prop: Continuous T)
   have ht : T 0=(0,p):=by simp [T]
   have hv := Filter.Tendsto.congr' hz (hq.continuousWithinAt); rw [Function.comp_apply,ht] at hv; exact tendsto_nhds_unique hv (show Tendsto (fun _=>_) _ (𝓝 (0:ℂ)) from tendsto_const_nhds)
lemma steer_vanish i j k a b c p: steer F i j k a b c p=0:= by
    rcases p with ⟨p,q⟩; let f:=steer F i j k a b c
    have hp : f (0,q)=0:= steer_origin X H hv i j k a b c q
    have hq : f (p,0)=0:= (steer_swap X i j k a b c p 0).trans (steer_origin X H hv j i k b a c p)
    have hu : Shape f (h-3):=steer_shape X i j k a b c
    rcases lt_trichotomy h 3 with hl|hl|hl
    · exact congr_fun (hu.charge (by omega)) _
    · subst h; calc
        _ = f (0,q):=(shape_constant hu _).trans (shape_constant hu _).symm
        _ = 0 := hp
    have h : h=4:= by omega
    rw [h] at hu; obtain ⟨T,hT⟩:=shape_linear hu; change f (p,q)=0; rw [hT,show (p,q)=(p,0)+(0,q) by simp,map_add,← show f (p,0)= _ from congr_fun hT _, ← show f (0,q)= _ from congr_fun hT _,hp,hq, add_zero]
end YM.MS.Landau.Detect.Mark
