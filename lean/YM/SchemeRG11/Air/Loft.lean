import YM.SchemeRG11.Air.Hatch
/-! Tower shores and recursion. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Air
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open Labels Long
open scoped Classical Pointwise
variable {G:Gauge}{m n:ℕ}{u v:ℤ}{T:Align.Itinerary}{R:ℝ}{f:Slate}
abbrev latch (T: Align.Itinerary)(v:ℤ):ℕ→ℝ:=fun i=> T.gap i ^ v
lemma hatch_iff {f:ℕ→ℝ}:f=O[atTop] (latch T u) ↔ ∃ C>0,∀ᶠ i in atTop,|f i|≤ C*T.gap i^u:=by
 simp only [isBigO_iff']; apply exists_congr; intro c; rw [and_congr_right_iff]; intro _; simp_rw [Real.norm_eq_abs,latch,abs_of_pos (zpow_pos (T.positive _) _)]
lemma hatch_vanish (p:u>0) : Tendsto (latch T u) atTop (𝓝 0):=by
 have hh:=T.cutoff.pow u.toNat; have he:u.toNat≠0:=by omega
 rw [zero_pow he] at hh; convert hh using 1; funext i; conv_lhs=> rw [← Int.toNat_of_nonneg p.le]; unfold latch; simp only [zpow_natCast]
lemma weaken_less {f:ℕ→ℝ}{p:ℤ}(h:f=O[atTop] latch T v)(hp:p+v>0): Tendsto (fun i=> (T.gap i)^p*f i) atTop (𝓝 0):=by
 have he: (fun i=> (T.gap i)^p*f i)=O[atTop] latch T (p+v):=by
    convert! (isBigO_refl (latch T p) _).mul h using 1; funext i; change _=latch _ p _ * _; rw [latch,zpow_add₀ (T.positive _).ne'] -- repair
 exact he.trans_tendsto (hatch_vanish hp)
lemma higher (u:ℤ)(p:u≥0):Finishes (latch T u):=by
 rcases eq_or_lt_of_le p with h|h; · rw [←h,show latch T 0=(fun _=>1) from funext (fun i=>zpow_zero _)]; exact Finishes.const _
 exact ⟨0,hatch_vanish h⟩
lemma noted (h:Local T R u v f)(hr:R>0)(x:Cover): (fun i=> f i x)=O[atTop] latch T u:=by
 obtain ⟨C,hC,H⟩:=h; apply hatch_iff.mpr; refine ⟨C*World.d x^v,mul_pos hC (zpow_pos (World.d_pos _) _),?_⟩
 filter_upwards [H,gate_const T hr x] with i h hp; rw [mul_right_comm C]; exact h x ((gate_iff T R i x).mp hp)
lemma march (hv:v≥0)(hp:(fun i=> f i 0)=O[atTop] latch T u)(he:∀ j:Axis,Local T R u v (fun i=> soar j (f i))): Local T R u (v+1) f:=by
 obtain ⟨B,hB,H⟩:= hatch_iff.mp hp; choose C hC ht using he; obtain ⟨c,hc⟩:=Finite.exists_max C
 refine ⟨B+4*C c,add_pos hB (mul_pos (by norm_num) (hC _)),?_⟩; filter_upwards [H,(eventually_all_finset Finset.univ).mpr (fun i _=> ht i)] with i hi hk x hx
 apply dial hv hB.le (hC _).le (f i) i hi _ x hx
 intro j p hp; exact (hk j (Finset.mem_univ _) p hp).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc j) (zpow_pos (T.positive i) _).le) (zpow_pos (World.d_pos _) _).le)
abbrev dove (s:Fliers)(f:Slate):Slate:=fun i=>fleet s (f i)
lemma pilgrim (h:∀s:Fliers,s.card ≥n → Local T R u ((n:ℤ)-s.card) (dove s f))(hp:∀s:Fliers,s.card<n →(fun i=> fleet s (f i) 0)=O[atTop] latch T u) (s:Fliers): Local T R u ((n:ℤ)-s.card) (dove s f):=by
 have he (k:ℕ) (z:Fliers)(hz:n≤z.card+k): Local T R u ((n:ℤ)-z.card) (dove z f):=by
    induction k generalizing z with
    | zero=> rw [add_zero] at hz; exact h _ hz
    | succ k ih=>
      by_cases ho:n≤z.card; · apply h z ho
      specialize hp z (by omega)
      rw [show (n:ℤ)-(z.card:ℤ)= n-(z.card+1:ℤ)+1 by omega]; apply march (by omega) hp
      intro j; specialize ih (j ::ₘ z) (by rw [Multiset.card_cons]; omega); rw [Multiset.card_cons,Nat.cast_add_one] at ih; convert ih using 1; funext i; unfold dove; rw [fleet_cons]; rfl
 exact he n s (by omega)
lemma capMaker (n:ℕ)(f:Plane ℝ): ∃p:Plane ℝ,p∈cap ℝ n∧∀s:Fliers,s.card<n→fleet s f 0=fleet s p 0:=by
 induction n generalizing f with
 | zero=> exact ⟨0,Submodule.zero_mem _,fun s h=>by omega⟩
 | succ n ih=>
   obtain ⟨p,P,H⟩:= peano n (fun s=>fleet s f 0)
   obtain ⟨q,Q,J⟩:= ih (f-p); refine ⟨q+p,Submodule.add_mem _ (cap_succ _ Q) P,?_⟩
   intro s h; rw [map_add,Pi.add_apply]; by_cases e:s.card=n
   · rw [H _ e,member.mp Q _ e]; simp
   have hh:=J s (by omega); rw [map_sub,Pi.sub_apply] at hh; abel_nf; linarith only [hh]
def Boarded (T:Align.Itinerary)(R:ℝ)(f:Slate):Prop:=∀s:Fliers,Local T R ((s.card:ℤ)+1) 0 (dove s f)
lemma billow {g:ℕ→ Plane ℝ}(he: ∀i,g i∈cap ℝ n)(h:Boarded T R f)(hp:∀s:Fliers,s.card<n→ (fun i=> fleet s (f i-g i) 0)=O[atTop] latch T (n+1)):∀ s:Fliers, Local T R (n+1) ((n:ℤ)-s.card) (dove s (f-g)):=by
 apply pilgrim _ hp; intro s hs
 have hh (i): fleet s (g i)=0:=member.mp (cap_height hs (he i)) s rfl
 rw [show dove s (fun i=> f i-g i)=dove s f from funext fun i=>by change fleet s (f i-g i)=fleet s (f i); rw [map_sub,hh i,sub_zero]]; convert Long.fold (h s) ((s.card:ℤ)-n) (by omega) using 1 <;> omega
end YM.SchemeRG11.Air
