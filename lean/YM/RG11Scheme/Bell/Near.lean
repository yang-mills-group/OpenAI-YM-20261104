import YM.RG11Scheme.Bell.Pole

/-! Newton interpolation remainder without evaluating a coefficient map on off-lattice columns. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Bell
open Function Set Lattice Mesh Stencil.Point Stencil.Shot
open scoped BigOperators Classical Topology
variable {E:Type}[NormedAddCommGroup E] {k d:ℕ}
lemma closes_zero {x:Cover} {C:ℝ} (hC:0≤C) {f:Cover→E}(h: ∀ i y, elev y≤elev x→ ‖f (y+step i)-f y‖≤ C): ‖f x-f 0‖ ≤ 4 * wide x * C := by
   have hb (y:Cover) : elev y≤elev x → ‖f y-f 0‖≤ (taxi y:ℝ)*C := by
       apply taxi_rule (P:=fun y=> elev y≤elev x → ‖f y-f 0‖≤(taxi y:ℝ)*C)
       · exact fun H=> by rw [sub_self,norm_zero]; positivity
       intro z t i he hu hw hn H
       have ht:= he (hu.trans H)
       have hs: ‖f z - f t‖≤C := by
          rcases hn with hn|hn
          · rw [hn]; exact h i t (hu.trans H)
          rw [norm_sub_rev,hn]; exact h i z H
       apply le_trans (b:=C+(taxi t:ℝ)*C) _; · rw [hw];push_cast; ring_nf; exact le_rfl
       exact (by rw [← sub_add_sub_cancel (f z) (f t) (f 0)];exact (norm_add_le ..).trans (add_le_add hs ht))
   refine (hb _ le_rfl).trans (mul_le_mul_of_nonneg_right ?_ hC)
   unfold wide; exact (show (taxi x:ℝ) ≤ 4*(elev x:ℝ) by exact_mod_cast (taxi_bound x)).trans (by linarith)
lemma divest {f:Cover→ E}{C:ℝ}(K : List Axis) (m:ℕ) (r:ℕ) (hC:0≤C) (hz:∀ (p:List Axis),p.length≤ m+K.length → go p f 0=0) (hv:∀ D:List Axis,D.length=m+K.length+1→∀ x,elev x≤r→ ‖go D f x‖ ≤ C) : ∀ x,elev x≤r→ ‖go K f x‖ ≤ (4*wide x)^(m+1)*C := by
    induction m generalizing K with
    | zero=>
       intro x hx; rw [zero_add,pow_one]
       have he:= closes_zero (f:=go K f) (x:=x) hC (fun i y hi=> hv (i::K) (by simp) y (hi.trans hx))
       simpa only [hz K (by omega),sub_zero] using he
    | succ m ih=>
       intro x hx; have hp:=wide_pos x
       have H : ‖go K f x-go K f 0‖ ≤ 4*wide x *((4*wide x)^(m+1)*C) := by
           apply closes_zero (by positivity)
           intro i y hv'
           have he := ih (i::K) (fun p hi=> hz p (by rw [List.length_cons] at hi; omega)) (fun D hD=> hv D (by rw [List.length_cons] at hD; omega)) y (hv'.trans hx)
           apply he.trans
           have hm : wide y ≤ wide x:= by unfold wide; exact_mod_cast add_le_add_left (show (↑(elev y):ℝ) ≤ (↑(elev x):ℝ) by exact_mod_cast hv') (1:ℝ) -- orientation?
           have hl:=wide_pos y; gcongr
       rw [hz K (by omega),sub_zero] at H; exact H.trans (le_of_eq (by rw [pow_succ];ring))
variable [NormedSpace ℝ E]
def grace (f g : Cover → E)(d:ℕ) := ∀ D:List Axis,D.length ≤ d → go D f 0= go D g 0
lemma gratis (f g : Cover → E)(h:grace f g d) (A:List Axis)(he:A.length≤d) : go A (f-g) 0=0 := by
   change ladder A (f-g) _ = _; rw [map_sub];exact sub_eq_zero.mpr (h _ he)
lemma core_exists [CompleteSpace E](f:Cover→ E)(d:ℕ): ∃ Y:Cover→ E, Y∈hill E d∧ grace f Y d := by
   induction d generalizing f with
   | zero => refine ⟨fun _=> f 0,hill_round 0 _,fun D hd=>?_⟩; simp [(List.length_eq_zero_iff.mp (by omega : D.length=0))]
   | succ m IH=>
     let T:=traces (cranium (m+1) f); obtain ⟨W,hW,he⟩:=IH (f-T)
     refine ⟨T+W,(hill E _).add_mem (traces_grade _) (hills (Nat.le_succ m) hW),fun D hD=>?_⟩
     by_cases ht:D.length=m+1
     · rw [plus_go, hW D (by omega : m<D.length)]; apply Eq.trans (skates _ f _ ht); rw [Pi.zero_apply,add_zero]
     have hp:=he D (by omega);change ladder D (f-T) _ = _ at hp;rw [map_sub,Pi.sub_apply, sub_eq_iff_eq_add] at hp; rw [plus_go,add_comm]; exact hp
lemma list_from {D:List Axis} {d} (he:D.length=d) : D=List.ofFn fun i : Fin d=>D.get ⟨i.val,he.symm ▸ i.isLt⟩ := by subst d; simp
abbrev Firing (d:ℕ) := Sigma (fun k:Fin (d+1)=>Fin k.val→Axis)
def clockL (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](d:ℕ) : ↥(hill E d) →ₗ[ℝ] (Firing d → E) := LinearMap.pi fun (s:Firing d)=> LinearMap.proj (0:Cover) ∘ₗ ladder (List.ofFn s.2) ∘ₗ (hill E d).subtype
lemma hill_lens (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (d:ℕ) : Injective (clockL E d) := by
    rw [← LinearMap.ker_eq_bot]; apply le_antisymm _ bot_le; intro v hv
    change clockL E d v=0 at hv
    have he : (v : Cover→ E)=0 := by
        refine (hill_readout v.property).2 (fun D hd=>?_)
        let m:Fin (d+1):=⟨D.length, Nat.lt_succ_of_le hd⟩
        let p:Firing d:=⟨m, D.get⟩
        nth_rw 1 [list_from (D:=D) (d:=D.length) rfl]; exact congrFun hv p
    exact show v=(0:↥(hill E d)) from Subtype.ext he
instance [FiniteDimensional ℝ E](d:ℕ) : FiniteDimensional ℝ ↥(hill E d):= FiniteDimensional.of_injective (clockL E d) (hill_lens E d)
lemma bounded [CompleteSpace E] (f:Cover→ E)(h:f ∈ hill E d): ∃ C≥0,∀ x, ‖f x‖ ≤ C * wide x^d := by
   induction d generalizing f with
   | zero => refine ⟨‖f 0‖,norm_nonneg _,fun x=>?_⟩; rw [hill_const_iff.mp h x,pow_zero,mul_one]
   | succ d IH=>
      let U := cranium (d+1) f
      obtain ⟨C,hC,h⟩ := IH _ (lowerings d h)
      refine ⟨C+‖U‖*2^(d+1),by positivity,fun x=>?_⟩
      have he : ‖traces U x‖≤‖U‖*(2*wide x)^(d+1) := by
         have hk:= axis_elev x
         apply (U.le_opNorm (fun _=>row x)).trans; rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; gcongr; unfold wide; linarith
      have ht := add_le_add (show ‖(f x-traces U x)‖ ≤ _ from h x) he
      calc _ ≤ ‖f x-traces U x‖+‖traces U x‖:= by simpa using norm_add_le (f x-traces U x) (traces U x)
           _ ≤ _ := ht
           _ ≤ _ := by rw [add_mul, mul_pow, mul_assoc]; gcongr; exact wide_one _; omega
end YM.RG11Scheme.Bell
