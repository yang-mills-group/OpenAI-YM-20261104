import YM.FormalBulk08.City.Paint

/-! Raw displacement powers and Maxwell price. Polynomial reserves from
one same-mesh width. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Cork
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {n: Side} {k : ℕ} {A σ : ℝ}

lemma pockets (N : ℕ) (hs : 0<σ) : ∃ C : ℝ, 0<C ∧ ∀ x≥(0:ℝ), (1+x)^N ≤ C * Real.exp (σ*x):= by
   rcases N with (_|m)
   · exact ⟨1,one_pos,fun x hx=>by simp [mul_nonneg hs.le hx]⟩
   let u : ℝ:= m+1; have hu:0<u:= by unfold u;positivity
   let t:=σ/u; have ht:0<t:= div_pos hs hu
   let C:=max 1 t⁻¹; have hc: 0<C:= lt_max_of_lt_left one_pos
   refine ⟨C^(m+1), pow_pos hc _,fun x hx=>?_⟩
   have hh : 1+x ≤ C*Real.exp (t*x):= by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hc.le)
      have he : 1 ≤ C*t:= by rw [← inv_mul_cancel₀ ht.ne']; exact mul_le_mul_of_nonneg_right (le_max_right ..) ht.le
      rw [mul_add,mul_one,← mul_assoc]; nlinarith only [he,mul_le_mul_of_nonneg_right he hx,(show 1≤C from le_max_left ..)]
   refine le_trans (pow_le_pow_left₀ (by positivity) hh (m+1)) ?_; rw [mul_pow,←Real.exp_nat_mul]; apply le_of_eq; congr 2;push_cast;unfold t u at *;field_simp

def Paddle (N : ℕ) (f : Cover→ℝ) (C : ℝ) := 0≤C ∧ ∀ v,‖f v‖≤C*(1+size v)^N
def Pad (f : Cover→ℝ):= ∃ N C, Paddle N f C
lemma flat_pad (a : ℝ): Pad (fun _ => a):= ⟨0,|a|,abs_nonneg _,fun _=>by simp⟩
lemma Pad.add {f g : Cover→ℝ}(h: Pad f)(hp: Pad g): Pad (f+g) := by
    obtain ⟨m,A,h,hA⟩:=h; obtain ⟨n,B,hp,hB⟩:=hp
    refine ⟨m+n,A+B,add_nonneg h hp, fun i=> (norm_add_le ..).trans ((add_le_add (hA i) (hB i)).trans ?_)⟩; rw [add_mul]; gcongr <;> simp
lemma Pad.mul {f g : Cover→ℝ}(h: Pad f)(hp: Pad g): Pad (f*g) := by
    obtain ⟨m,A,h,hA⟩:=h; obtain ⟨n,B,hp,hB⟩:=hp
    refine ⟨m+n,A*B,mul_nonneg h hp, fun i=>?_⟩; rw [Pi.mul_apply,norm_mul,pow_add,mul_mul_mul_comm]; exact mul_le_mul (hA i) (hB i) (norm_nonneg _) (by positivity)
lemma Pad.smul {f : Cover→ℝ}(h : Pad f)(c : ℝ):Pad (c • f):= (flat_pad c).mul h
lemma Pad.pow {f : Cover→ℝ}(h : Pad f)(n):Pad (f^n):=by induction n with
   | zero=> rw [pow_zero]; exact flat_pad 1
   | succ n ih=> rw [pow_succ];apply ih.mul h
lemma Pad.shift {f : Cover→ℝ}(h : Pad f)(a : Cover):Pad (fun v=> f (v+a)):= by
    obtain ⟨m,A,h,hA⟩:=h; refine ⟨m,A*(1+size a)^m,by positivity,fun i=> (hA _).trans ?_⟩; rw [mul_assoc,←mul_pow]; gcongr; have hh : (((size (i+a)):ℕ):ℝ) ≤ size i+size a := by exact_mod_cast size_add i a
    nlinarith only [hh, mul_nonneg (Nat.cast_nonneg (α:=ℝ) (size i)) (Nat.cast_nonneg (size a))]

def ch (a:Axis)(x:Cover):ℝ:= x a
lemma ch_cap (a): Paddle 1 (ch a) 1:= by
   refine ⟨zero_le_one,fun i=> ?_⟩; have he : ‖ch a i‖≤ (size i:ℝ):= by rw [ch,Real.norm_eq_abs,←Int.cast_abs,← Int.natCast_natAbs];exact_mod_cast (Finset.single_le_sum (f:=fun k:Axis=> (i k).natAbs) (fun k _=>Nat.zero_le _) (Finset.mem_univ a))
   exact le_trans he (by rw [one_mul,pow_one]; linarith only)
lemma Pad.ch (a): Pad (Cork.ch a):= ⟨1,1,ch_cap a⟩

abbrev Slopes (G : Gauge):= Tile (edgeL G) 2
def hem (T: Slopes G) (b a:Axis)(i j:hue G)(v:Cover) := T ![(v,coord b,i),(0,coord a,j)]
lemma hem_pay (N : ℕ) (hs : 0<σ) : ∃ C : ℝ,0<C ∧ ∀ f D,Paddle N f D→∀ (T : Slopes G) A,Bail (fame _) σ T A → ∀ b a i j,(∑' v, ‖hem T b a i j v * f v‖ₑ) ≤ ENNReal.ofReal (A*(D*C)):= by
   obtain ⟨C,hc,h⟩:= pockets N hs
   refine ⟨C,hc,fun f D hp T A H b a i j=>?_⟩
   let F : Cover → pack (1:Fin 2) (show edgeL G from (0,coord a,j)):= fun v=>⟨![(v,coord b,i),(0,coord a,j)],rfl⟩
   have hf : Injective F:= fun v w ht=>congr_arg (fun u=> (u.val 0 : edgeL G).1) ht
   have hD:= hp.1; rw [ENNReal.ofReal_mul H.1]; refine le_trans ?_ (mul_le_mul_left (H.watch F hf) _)
   rw [←ENNReal.tsum_mul_right]; refine ENNReal.tsum_le_tsum fun v=>?_ ; have he : wide (fame _) (F v).val=size v:= by rw [peg_round]; change size (v-0)=_; rw [sub_zero]
   rw [glitter,he,enorm_mul]; have ht : ‖f v‖ ≤ Real.exp (σ*size v)*(D*C):=by
       refine ((hp.2 v).trans (mul_le_mul_of_nonneg_left (h _ (Nat.cast_nonneg ..)) hp.1)).trans_eq ?_ ;ring
   rw [mul_comm (shine ..),mul_assoc]; apply mul_le_mul_right; rw [Gorge.shine,←ENNReal.ofReal_mul (Real.exp_pos _).le,← ofReal_norm]; exact ENNReal.ofReal_le_ofReal ht

-- field sum

def net (T : Slopes G) (b a:Axis)(i j:hue G)(f:Cover→ℝ):= ∑' v,hem T b a i j v*f v
lemma net_funding (N : ℕ) (hs : 0<σ) : ∃ C : ℝ,0<C ∧ ∀ f D,Paddle N f D→∀ (T : Slopes G) A,Bail (fame _) σ T A → ∀ b a i j,|net T b a i j f| ≤ A*(D*C):= by
   obtain ⟨C,hC,H⟩:=hem_pay (G:=G) N hs
   refine ⟨C,hC,fun f D hp T A h b a i j=>?_⟩
   exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg h.1 (mul_nonneg hp.1 hC.le))).mp ((by rw [←Real.norm_eq_abs,ofReal_norm]; exact enorm_tsum_le_tsum_enorm.trans (H f D hp T A h b a i j)))

def Purse (T : Slopes G):= ∃ σ A,0<σ ∧ Bail (fame _) σ T A
lemma Purse.sum {T : Slopes G} (h:Purse T) (b a i j) {f} (hp:Pad f): Summable (fun v=> hem T b a i j v*f v):= by
    obtain ⟨σ,A,hσ,H⟩:=h; obtain ⟨N,D,hp⟩:= hp;obtain ⟨C,hc,hp'⟩:=hem_pay (G:=G) N hσ; exact (tsum_enorm_ne_top_iff_summable_norm.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hp' f D hp T A H b a i j))).of_norm
lemma net_add {T S: Slopes G}(h:Purse T)(e:Purse S)(b a i j){f}(hp:Pad f): net (T+S) b a i j f=net T b a i j f+net S b a i j f := by rw [net,net,net,←(h.sum b a i j hp).tsum_add (e.sum b a i j hp)]; simp only [hem,Pi.add_apply,add_mul]
lemma net_sub {T S: Slopes G}(h:Purse T)(e:Purse S)(b a i j){f}(hp:Pad f): net (T-S) b a i j f=net T b a i j f-net S b a i j f := by rw [net,net,net,←(h.sum b a i j hp).tsum_sub (e.sum b a i j hp)]; simp only [hem,Pi.sub_apply,sub_mul]
lemma net_smul (c : ℝ)(T: Slopes G)(b a i j f): net (c • T) b a i j f=c*net T b a i j f := by simp only [net,hem,Pi.smul_apply,smul_eq_mul,mul_assoc,tsum_mul_left]
lemma add_net {T: Slopes G}(h:Purse T)(b a i j){f g}(hp:Pad f)(hq:Pad g): net T b a i j (f+g)=net T b a i j f+net T b a i j g := by rw [net,net,net,←(h.sum b a i j hp).tsum_add (h.sum b a i j hq)]; simp only [Pi.add_apply,mul_add]
lemma smul_net (T: Slopes G)(b a i j)(f : Cover→ℝ)(c : ℝ) : net T b a i j (c • f)=c*net T b a i j f := by rw [net,net,← tsum_mul_left]; exact tsum_congr fun v=> mul_left_comm _ _ _
end YM.FormalBulk08.Cork
