import YM.X.Reed.Ahead
/-!
Difference bound auction. Supports uniform Taylor remainder with local-scale counting.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Reed
open Lattice Wilson Stems Next.Rank.CellsInt Next.Rank.Beamer Tensor TensorProduct Filter MeasureTheory Metric Finset Function Maxwell Asymptotics
open scoped Topology ContDiff BigOperators
variable {G:Gauge} {V:Type*} [NormedAddCommGroup V][NormedSpace ℝ V] {n k m:ℕ}
-- ∗blobs∗
def Tame (w f: Cover→V)(R:ℕ)(C:ℝ) := ∀ z:Cover, street z≤R→ ‖f z‖≤ C* ‖w z‖ -- maybe no
abbrev day (p:Cover):ℝ:=1+(street p:ℝ)
lemma day_pos(p:Cover):0<day p:= by unfold day; positivity
lemma day_me(p:Cover):1≤day p:= by unfold day; exact le_add_of_nonneg_right (by positivity)

omit [NormedSpace ℝ V] in
lemma cast_size (f:Cover→V)(R:ℕ)(C:ℝ)(hc:0≤ C)(h:∀ t:Cover,street t ≤R→∀ i, ‖stepValue f i t‖ ≤ C*day t^n)(v:Cover)(hv:street v≤R):
     ‖f v-f 0‖≤ (street v:ℝ)*(C*day v^n):= by
    have he (j:ℕ)(v:Cover)(hv:street v=j)(hr:j≤R):‖f v-f 0‖ ≤ (j:ℝ)*(C*day v^n):= by
      induction j generalizing v with
      | zero=> obtain h|⟨w,hw,_⟩:=strolling v; swap; · omega
               simp [h] -- indent?
      | succ j IH=>
        obtain hz|⟨w,hw,i,HH⟩:=strolling v
        · rw [hz]; simp only [sub_self,norm_zero]; positivity
        have H: street w=j:= by omega
        have hh : C*day w^n ≤ C*day v^n:=by unfold day; gcongr; omega
        have hj := IH w H (by omega)
        have hd : ‖f v - f w‖ ≤ C*day v^n:= by
           cases HH with
           | inl ht=> exact ht ▸ (show ‖f (w+step i)-f w‖ ≤ C*day (w+step i)^n from (h w (by omega) i).trans (ht ▸ hh))
           | inr ht=> rw [norm_sub_rev]; exact ht ▸ (h v (by omega) i)
        push_cast; apply (le_trans (norm_sub_le_norm_sub_add_norm_sub ..) (add_le_add hd hj)).trans -- explicit
        nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) j)]
    exact he _ v rfl hv

local notation "L"=> (atTop:Filter ℕ)
def OnStreet (R:ℕ→ℕ)(C: ℕ→ℝ) (n:ℕ)(f:ℕ→ Cover→ V): Prop:=∃ b,0≤b∧ ∀ᶠ k:ℕ in L, ∀ z:Cover,street z≤ R k→ ‖f k z‖≤ b* (‖C k‖*day z^n)
omit [NormedSpace ℝ V]
variable {R:ℕ→ℕ} {C:ℕ→ℝ}{f g:ℕ→Cover→V}
namespace OnStreet
lemma add (h:OnStreet R C n f)(p:OnStreet R C n g):OnStreet R C n (f+g):= by
    obtain ⟨b,hb,h⟩:=h; obtain ⟨a,ha,p⟩:=p; refine ⟨b+a,add_nonneg hb ha,?_⟩; filter_upwards [h,p] with k hk hp z hz; rw [add_mul]; exact (norm_add_le ..).trans (add_le_add (hk z hz) (hp z hz))
lemma move {g:ℕ→Cover→V}(h:OnStreet R C n f)(p:f =ᶠ[L] g):OnStreet R C n g:= by
    obtain ⟨b,hb,h⟩:=h; refine ⟨b,hb,?_⟩; filter_upwards [p,h] with k hp hk; rwa [← hp]
lemma zero : OnStreet R C n (0:ℕ→Cover→V):=⟨0,le_rfl,by simp [norm_zero]⟩
lemma constant {f:ℕ→V}(h:f =O[L] C): OnStreet R C n (fun k _=> f k) := by
    obtain ⟨b,hb,h⟩:= h.exists_pos; refine ⟨b,hb.le,h.bound.mono ?_⟩; intro k hk z hz; exact hk.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (day_me z))) hb.le)
lemma ground {z:Cover}(h:OnStreet R C n f)(p:∀ᶠ i in L, street z≤ R i): (fun k=> f k z)=O[L] C:= by
    obtain ⟨b,hb,h⟩:=h; apply isBigO_iff.mpr; refine ⟨b*day z^n, (h.and p).mono ?_⟩; intro k ⟨hk,hp⟩; apply le_trans (hk z hp); rw [mul_assoc, mul_comm _ ‖C k‖]
lemma of_step (h: (fun k=> f k 0)=O[L] C)(p:∀ i:Axis, OnStreet R C n fun k=>stepValue (f k) i): OnStreet R C (n+1) f := by
    obtain ⟨s,hs,h⟩:=h.exists_pos; choose c hc Hp using p; let b:=∑ i:Axis,c i; have hb:0≤b:=sum_nonneg fun i _=> hc i
    refine ⟨s+b, add_nonneg hs.le hb, ?_⟩; filter_upwards [eventually_all.mpr Hp,h.bound] with k hk ht z hz
    have hu : ‖f k z - f k 0‖ ≤ (street z:ℝ)*(b* ‖C k‖*day z^n):= cast_size _ (R k) _ (by positivity) (fun v hv i=> (hk i v hv).trans (by rw [mul_assoc]; apply mul_le_mul_of_nonneg_right (single_le_sum (fun i _=> hc i) (mem_univ i)) (by have :=day_pos v; positivity))) z hz
    calc
      _ ≤ ‖f k z-f k 0‖ + ‖f k 0‖:= by simpa only [sub_add_cancel] using norm_add_le (f k z-f k 0) (f k 0)
      _ ≤ _:= by
        apply le_trans (add_le_add hu ht); rw [add_mul];
        rw [add_comm ((street z:ℝ)* _)]
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (day_me z))) hs.le
        ·  calc
          _ ≤ day z*(b* ‖C k‖*day z^n):= mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by have :=day_pos z; positivity)
          _ = _:= by rw [pow_succ]; ring
end OnStreet
end YM.PositionX.Reed
