import YM.FormalBulk08.Avenue.Kill
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
variable {x:Loc G 1}{η σ A B C:ℝ}{u r p:ℕ} {q:edgeL G→edgeL G→ℝ}
-- exact Kalm & cream for any test mark at leading
open City PowerSeries
variable {S:Side→ Type*}
def jolt_chill {V:Type*}(q:Jolt V S) (N:Side→Side)(h:Tendsto N atTop atTop): Jolt V (S∘N):= ⟨fun _=>q.give _,fun _=>q.undo _,fun _=>q.back _,fun x=> h.eventually (q.tame x)⟩
variable {I:Type*}
-- field reroot bounded L¹ tail
lemma penny_keep (o:Biglot I)(M:Tile (Tor n I) r)(h: Knoxville (lake n I) η (Lotus.drip n o) M A)(hs:0≤η)(v:chain (Tor n I) r): ‖M v‖ ≤ (Real.exp (η*size o.1)*A)*∏ i,coast (η/(r+1:ℝ)) (boil n (v i)):= by
   let k:= (glaze I r).undo n v; let u:=size o.1; let s:=(r+1:ℝ); have hh:0<s:=by unfold s; positivity
   let V : chain (Tor n I) (r+1):=Fin.cons (Lotus.drip n o) v
   let L:= wide (lake n I) V; let W:ℕ:=∑ i,size (k i).1
   have ht:W≤(r+1)*(L+u):= by
       have he (i:Fin r): size (k i).1 ≤ L+u:= (skit_anchor n V 0 i.succ).trans (Nat.add_le_add_left (skirt ..) L)
       apply (Finset.sum_le_sum (fun i _=>he i)).trans; simp [add_mul]
   have hp : (W:ℝ) ≤ s*((L:ℝ)+u):= by unfold s;exact_mod_cast ht
   change _ ≤ (Real.exp _*A)*∏ i, coast (η/s) (k i); apply (le_div_iff₀ (Real.exp_pos _)).mpr (show ‖M v‖*Real.exp (η*L) ≤ A from penn_chill v h) |>.trans
   rw [div_eq_mul_inv,← Real.exp_neg,mul_comm _ A,mul_assoc A, prod_shine k, ←Real.exp_add]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) h.1; change -(η*L) ≤ η*u + -(η/s)*W; field_simp; nlinarith
lemma pillars [Fintype I]{x:Biglot I}(F:(n:Side)→ Tile (Tor n I) r)(hp: Vent x F η A)(hs:0<η)(hv:Light 0 F)(N:Side→ Side)(ht:Tendsto N atTop atTop)(M:(n:Side)→ Tor (N n) I → S n→ℝ)(H:∀ n i j,‖M n i j‖≤C)(hc:0≤C)(v:(n:Side)→ chain (S n) r): Tendsto (fun n=> pearl (M n) (F (N n)) (v n)) atTop (𝓝 0) := by
    let E:= jolt_chill (glaze I r) N ht; let s:=η/(r+1:ℝ); have he:0<s:=by unfold s; positivity
    let B:=(Real.exp (η*size x.1)*A); have hA:= hp.exists.choose_spec.1; have hB:0≤ B*C^r:= by unfold B; positivity
    let R n (w:chain (Tor (N n) I) r):= ∏ i:Fin r,M n (w i) (v n i)
    have hr n (w:chain (Tor (N n) I) r): ‖R n w‖ ≤ C^r:= by unfold R;rw [norm_prod]; simpa using Finset.prod_le_prod (s:=Finset.univ) (fun i _=> norm_nonneg (M n (w i) (v n i))) (fun i _=>H n _ _)
    let D (x:chain (Biglot I) r):= (B*C^r) * ∏ i,coast s (x i)
    let T n (w:chain (Tor (N n) I) r):=F (N n) w*R n w
    change Tendsto (fun n=> ∑' w,T n w) _ _; rw [show (𝓝 (0:ℝ))=𝓝 (∑' _u:chain (Biglot I) r, (0:ℝ)) by simp]; apply jolt_limit E T (fun _=>0) D ((monsoon he).mul_left _) (fun i=> mul_nonneg hB (Finset.prod_nonneg (fun i _=>(Real.exp_pos _).le))) ?_ ?_
    · intro i; let q n:= F (N n) (E.give n i);have hx : Tendsto q atTop (𝓝 0):= (hv i).comp ht
      rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero (fun i=> norm_nonneg _) (fun n=>?_ ) (show Tendsto (fun i=> ‖q i‖ * C^r) atTop (𝓝 (0:ℝ)) from (by simpa only [norm_zero,zero_mul] using (hx.norm).mul_const (C^r)))
      unfold T; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hr n _) (norm_nonneg (q n))
    filter_upwards [ht.eventually hp] with n hn x'; unfold T; rw [norm_mul]; refine (mul_le_mul (penny_keep _ _ hn hs.le x') (hr _ x') (norm_nonneg _) (mul_nonneg (mul_nonneg (Real.exp_pos _).le hA) (Finset.prod_nonneg (fun _ _=> (Real.exp_pos _).le)))).trans_eq (mul_right_comm B _ _)
lemma still_raft [Fintype I] {x:Biglot I}{T:Tile (Biglot I) r}{F Z:(n:Side)→Tile (Tor n I) r}(h:Kalm η x T F)(hs:0<η)(hu:0<σ)(H:Kalm σ x T Z)(N:Side→Side)(ht:Tendsto N atTop atTop)(M:(n:Side)→Tor (N n) I→S n→ℝ)(hp:∀ n i j,‖M n i j‖≤C)(hc:0≤C)(v:(n:Side)→chain (S n) r) : Tendsto (fun n=>pearl (M n) (F (N n)) (v n)-pearl (M n) (Z (N n)) (v n)) atTop (𝓝 0) := by
   obtain ⟨h,B,hB⟩:=h; obtain ⟨hp',U,hU⟩:=H; let F' n:= F n-Z n; let δ:=min η σ; have he:0<δ:= lt_min hs hu
   have hv(n:Side): pearl (M n) (F' (N n)) (v n)=pearl (M n) (F (N n)) (v n)-pearl (M n) (Z (N n)) (v n):= by unfold pearl F';simp_rw [Pi.sub_apply,sub_mul,tsum_fintype,Finset.sum_sub_distrib]
   simp_rw [←hv]; refine pillars F' (A:=B+U) ((hB.and hU).mono (fun i hi=> penn_sub (penn_shrink hi.1 (min_le_left ..)) (penn_shrink hi.2 (min_le_right ..)))) he ?_ N ht M hp hc v; intro u; have hk:= (h u).sub (hp' u); rw [sub_self] at hk; exact hk
end YM.FormalBulk08.Avenue
