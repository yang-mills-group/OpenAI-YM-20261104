import YM.Qlocal.Versal.Vienna
/-! `StoryNear` term.Phi.Cabinet.State on REAL.Current calendar.Basic. Later assembler of REAL/Lens Transfer Semantic.En. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet
open Function Filter Lattice Laurent RG Wilson Stationary Lasso Zora Work.F02 Metric
open Marker Multi Finset Extra.Iteration
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze ConnectedActivityE6 AnalyticBridge
variable {V:Type}[DecidableEq V] {ι E:Type} {G:Gauge}{k n j r i z w:ℕ} {c:Side} {d t a v u C φ g:ℝ}{R:Census V}
namespace Tale
variable (p:BudgetPoint)(l:Lattice.Order)(s:Senses R)(A:Tale R G) (X:A.Decision)(o:V→Site c)(x:Site c)(W:Config G c)
set_option quotPrecheck false
local notation "I"=>Fin (A.depth+1)
set_option quotPrecheck false
local notation "J" i=> Fin (Fin.val i+Lagger.dues A.power s.val+1)
variable (i:Fin (A.depth+1))(n:Fin (i.val+Lagger.dues A.power s.val+1))
local notation "A★"=> A.array s i n
local notation "K"=> Sonnet.root s
local notation "S"=> o K
local notation "m"=> A.method
local notation "Ψ"=> A.stampE s i n
local notation "κ"=> A.boom s
local notation "θ"=> p.threshold
local notation "C₀"=> Tale.court p.B S
local notation "u!"=>A.short X k
local notation "u₀"=>A.long X k
local notation "u₁"=>κ
local notation "p₀"=> g^Ψ/g^κ
local notation "P!"=> termR s A u! o i n g
-- Mask reservation charged once per total label, not length.
noncomputable abbrev grand (v a C g:ℝ):= ∑ i:I,∑ n:J i,gold p G m n.val i.val v a C g
include l
lemma shortBook (h:t/p.B≤d)(he:0≤t)(hd:0≤d)(ha:0<a)(hv:0≤v)(ht: Allows A (d+a+v) C) (hk:k≤p.B)(hx:0<g) : PayR p (C₀) (grand p s A t a C g * Real.exp (-(t*coverNumber p.B (C₀)))) (wake s A u! o g):= by simp_rw [grand, Finset.sum_mul,wake]; exact PayR.sum univ _ _ fun i _=> PayR.sum univ _ _ fun n _=> paid p l s A X o _ _ h he hd ha hv (ht.pay ..) hk hx
omit l
lemma evacuated (h:¬Live o s k): wake s A u! o g=0:= by unfold wake; exact Finset.sum_eq_zero fun i hi=> Finset.sum_eq_zero fun n hn=> thaw s A X o i n h
lemma vestments(h:Live o s k) {S': V→Support c}(hS:∀ i∈ essence s,S' i⊆ Tale.court (p.B-k) (o i))(hk:k≤p.B): ∀ i∈essence s,S' i⊆ (C₀) := by
 intro i hi z hz; have he:=hS i hi hz; apply halo_spec.mpr ⟨S,mem_singleton_self _,?_⟩; have hv: separation (o i) z ≤ p.B-k:= by simpa only [Tale.court,halo_spec,mem_singleton,exists_eq_left] using he
 have hu:=h i hi; apply le_trans (separation_triangle S (o i) z) (by omega)
-- near stamp habitat compiled.Other α tickets.Holding pending.Need depend on exponent case mask exact.
-- continuation tail term.
variable (S': V→Support c)
abbrev speaks (k:ℕ) (j:ℕ): Prop:= X s i n j ∧ k < (A★ j).momentum ∧ ((A★ j).stage.Hears o)
local notation "h[" j "]"=> speaks s A X o i n k j
noncomputable def canvas (j:ℕ)(k:ℕ) : Support c:= if speaks s A X o i n k j then Vase.cloak l (A★ j) S S' else Tale.court p.B S -- if missing, dummy with x, no stencil. Ledger assembler later.
noncomputable def tint (j:ℕ)(k:ℕ)(g:ℝ): Config G c→ℝ:= if speaks s A X o i n k j then (g^Ψ/g^κ) • (A★ j).read S m else 0
noncomputable def expenses (j k b:ℕ)(g:ℝ) : ℝ:= if speaks s A X o i n k j then |g^Ψ/g^κ| *Vase.Sus (A★ j) p m b else 0
local notation "T"=>tint s A X o i n
local notation "Can"=> canvas p l s A X o i n S'
local notation "Ez"=> expenses p s A X o i n
lemma vest (hg: Album.Health (A★) a C)(h:0<a) (k:ℕ): HasSum (fun j=>(T j k g) W) (termR s A (A.long X k) o i n g W):= by
 let P j := speaks s A X o i n k j; let h0(j:ℕ):=(A★).readout P S m j W; have hh: P=(fun j=> (A.long X k) s i n j ∧ (A★ j).stage.Hears o):= by ext; simp only [P, long, speaks,and_assoc]
 have hv : HasSum h0 (playing A (A.long X k) o s i n W):=(by rw [show playing A (A.long X k) o s i n W= Album.realize P (A★) S m W from by unfold playing Album.picture; rw [hh]]; exact ((A★).global_sum P S W m hg h).hasSum)
 refine HasSum.congr_fun (hv.const_smul p₀) (fun j=>?_); unfold tint; split
 next h=> simp only [Pi.smul_apply]; unfold h0 Album.readout; rw [if_pos h]
 next h=> unfold h0 Album.readout; rw [if_neg h]; simp
-- separation collars.Frame.C.Cover.Parameter `C`, `z`,`t` etc.
variable {D b K0 a₀ : ℕ}
variable (hR : ∀ i∈essence s,S' i⊆Tale.court b (o i)) (hC : ∀ i∈essence s,coverNumber p.B (S' i) ≤ D) (hS:∀ i∈essence s,o i∈S' i)
noncomputable abbrev geoD (s:Senses R)(n D:ℕ): ℕ:= 1+(essence s).card+n+D*(essence s).card
local notation "D₀"=> geoD s n.val D
local notation "Σ!"=> Vase.humid G p.power p.order n.val A.method b D₀ t a
-- above D shadows.Maybe. avoid
include hR hC hS l
lemma frugal (hc:0≤t)(hd:0≤d)(hv:0≤u)(ha:0<a)(hk:t/p.B≤d)(ht: Album.Health (A★) (a+d+v+u) C)(hP:0<g)(hg:0≤v):
    (∀ j, PayR p (Can j k) (Ez j k b g) (T j k g) ∧ S ∈ (Can j k)) ∧ SumBudget (fun j=> Ez j k b g * Real.exp (t*coverNumber p.B (Can j k)+ u*(A★ j).momentum)) (g^i.val*(θ/g)^n.val * Vase.humid G p.power p.order n.val A.method b (geoD s n.val D) t a *C*Real.exp (-(v*k))) := by
 let H:=Vase.humid G p.power p.order n.val m b (geoD s n.val D) t a; let L:ℝ:=g^i.val*(θ/g)^n.val; let Γ u:=a+d+v+u
 have hp:0≤p₀:= by positivity
 have hf(j:ℕ)(h:h[j]): Vase.Carrier l (A★ j) S (geoD s n.val D) b p.B (Can j k):= by rw [canvas, if_pos h]; exact Vase.cloaked l _ o S' h.2.2 p.B_pos hR hC hS
 have hy(j:ℕ):0≤Ez j k b g:= by
   unfold expenses; split
   next h=> exact mul_nonneg (abs_nonneg _) (Vase.Suspend l (A★ j) S p (hf j h) m).1
   next _=> rfl
 constructor
 · intro j; by_cases h:h[j]; swap; · rw [canvas, expenses,tint,if_neg h,if_neg h,if_neg h]; exact ⟨PayR.zero .., halo_subset _ _ (mem_singleton_self _)⟩
   refine ⟨?_,(hf j h).complete ((A★ j).birthplace ..)⟩; obtain ⟨hs,hu,hP⟩ := Vase.Suspend l (A★ j) S p (hf j h) m; rw [expenses,tint,if_pos h,if_pos h]; exact PayR.z_m _ ⟨hs,hu,hP⟩
 rw [mul_right_comm (L*H)]; let f(j):=(Can j k); apply Cost.mono (Cost.scale ht (L*H*Real.exp (-(v*k))) (mul_nonneg (mul_nonneg ?_ ?_) (Real.exp_nonneg _))) (fun j=> mul_nonneg (hy j) (Real.exp_nonneg _))
 rotate_left 1
 -- args order beware
 · exact (mul_nonneg (pow_nonneg hP.le _) (pow_nonneg (div_nonneg p.threshold_pos.le hP.le) _))
 · exact Vase.humid_nn G p.power p.order n.val m b D₀ t ha
 intro j; let Q:=(A★ j); by_cases h:h[j]; swap; · rw [expenses,if_neg h,zero_mul]; unfold L H; have he:=ht.1 j; have ht:= Vase.humid_nn G p.power p.order n.val m b D₀ t ha; have hx:=p.threshold_pos; positivity
 let v':ℝ:=u+v; let w:= v*k; let r:ℝ:= t*coverNumber p.B (Can j k)+ u*Q.momentum
 have he:= Vase.economical (u:=v') l (A★ j) S p (hf j h) A.method ha hc hk; rw [show d+a+v'=Γ u from (by unfold Γ v'; ring)] at he; rw [expenses, if_pos h, abs_of_nonneg hp]
 apply le_of_mul_le_mul_right ?_ (Real.exp_pos w)
 rw [show _= _ from (?_: L * H * Real.exp (-(v*k))*(A★ j).fare _*Real.exp w = L*H*(A★ j).fare (Γ u))]; swap; · rw [show v*(k:ℝ)=w from rfl,mul_right_comm (L*H),mul_assoc (L*H*_),← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
 -- pole equality
 rw [mul_assoc p₀, mul_assoc p₀]; unfold L; rw [← pole p s A i n hP, mul_assoc p₀, mul_assoc p₀]
 apply mul_le_mul_of_nonneg_left _ hp; apply le_trans ?_ he; rw [mul_assoc,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (Vase.Suspend l (A★ j) S p (hf j h) m).1; unfold w v'; apply Real.exp_le_exp.mpr; nlinarith only [hg,show (k:ℝ)≤(A★ j).momentum from (by exact_mod_cast h.2.1.le)]
end Tale
end YM.Qlocal.Quipu.Sonnet
