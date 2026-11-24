import YM.FormalBulk08.Sierra.Camping

/-! Expenses for OT. The unchanged factor decrements without a
copy of T yet-to-be-solved when r≥1; r=0 accounted separately. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{e E u l r d j t D:ℕ} {P:Patch} {B C U σ η:ℝ} {ε : ℝ≥0} {T: Pot G}
def Peaks (e r:ℕ)(T: Pot G)(o:edgeL G)(u:ℕ)(ε:ℝ≥0)(B:ℝ):= 0≤B ∧∀ i<e,∀ j:ℕ,1≤j → j ≤ r→ Knoxville (grain (fame _) ε) u o (T i j) B
structure Perusal (K:KernelChoices)(F:Flight j t)(V:Lodge F.patch)(u l e r:ℕ)(G:Gauge)(μ B:ℝ):Prop where
    mark:∀ T:Pot G,Ritual T l→∀ κ:Loc G 1,∀ o:edgeL G,∀ (ε θ:ℝ≥0), ε ≤ 1 →θ ≤ 1 → ε≤ F.L.val*θ → ∀ A C:ℝ,Knoxville (grain (fame _) θ) u o (T e r) A→ Peaks e r T o u θ C → Knoxville (grain (fame _) ε) u (chief F o κ) (Det F V K (T e r)) (μ*A+B*C)
structure Hearth (K:KernelChoices)(P:Patch)(V:Lodge P)(u R E j t:ℕ)(G:Gauge) (B:ℝ): Prop where
    nonneg:0≤ B
    merrit : ∀ r,1≤r → r≤R+E → ∀ l≤R,∀ e≤E,∀ F:Flight j t,∀ U:Lodge F.patch,∀ h:F.patch=P,h ▸ U=V → Perusal K F U u l e r G (Dove.Mulct F.L) B
lemma review_mono {F: Flight j t}{M:Lodge F.patch}(h:Perusal K F M u l e r G U B)(he:B≤C): Perusal K F M u l e r G U C:= ⟨fun T hv κ o a b hx hP hh _ _ hz ht=> Knoxville.mono (h.mark T hv κ o a b hx hP hh _ _ hz ht) (add_le_add_right (mul_le_mul_of_nonneg_right he ht.1) _)⟩

lemma groove (F:Flight j t)(κ:Loc G 1)(o:edgeL G)(hp:(Flight.duo K.penalty F).A0.strip η (C*(F.L.val:ℝ)⁻¹))(hs:0<η)(hc:0≤C)(hr:1≤r){ε θ:ℝ≥0}(hh:ε≤1)(he:ε≤F.L.val*θ){T:Tile (edgeL G) r}(h: Knoxville (grain (fame _) θ) u o T B): Knoxville (grain (fame _) ε) u (chief F o κ) (pearl (Chapel.merit (chair F G K)) T) ((Real.exp ((u:ℝ)*plum 1 8)*(sack u η*(Fintype.card (Loc G 1)* C))^r)/(F.L.val:ℝ)*B):= by
    have hv:0≤ C*(F.L.val:ℝ)⁻¹:= by positivity
    apply Knoxville.mono (icy_counts (u:=u) (fun _:Fin r=> chair F G K) o κ hh he T h hs (fun _=> grown_budget G _ hv hp) hv); let A:= Real.exp ((u:ℝ)*plum 1 8); let P:=sack u η*(Fintype.card (Loc G 1)*C)
    have hP :0≤ P:=mul_nonneg (sack_pos _ hs) (by positivity)
    let L:ℝ:=(F.L.val:ℝ)⁻¹
    rw [show sack u η*(Fintype.card (Loc G 1)*(C*(F.L.val:ℝ)⁻¹))=P*L from ?_, mul_pow]; swap; · unfold P L;ring
    have hz: L ≤ 1:= inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr F.L.pos)
    have hv: L^r≤L:= (pow_le_pow_of_le_one (by unfold L;positivity) hz hr).trans_eq (pow_one _)
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv (pow_nonneg hP _)) (mul_nonneg (Real.exp_pos _).le h.1)).trans_eq (by unfold L P;ring)
-- marker soak B uniform over all fine root x. `Sable.soak` constant independent o? existential C constructed independent of o, but type! Need pay POLY coil root x as data or strengthen. Translation invariance of T no. use carried R.Mesh v:= -o.1 and restore via Fee.
lemma from_R (T:Pot G)(m:ℕ)(h:Ritual T m)(x: Cover):Ritual (Kemp.work x T) m:= by
    have he: Young (Kemp.work x T) m:=by intro e r ha;apply h.young;intro hv;unfold Kemp.work at ha; rw [hv] at ha;exact ha rfl
    refine ⟨he,fun i j v s=>carrying _ s (h.committees i j) v,fun o i j=> ?_, fun n=>?_⟩
    · obtain ⟨s,A,hs,hp⟩:= h.health o i j; exact ⟨s,_,hs,penn_move (mantle_pay (o:=o) x hp) hs.le⟩
    rw [seated x T m n h.young h.committees]; simpa using repulp (wrap n x) 1 _ _ (h.esteem n)
lemma soak_hot (u e r l:ℕ)(G:Gauge) :∃ C:ℝ,0≤C ∧∀ T:Pot G,Ritual T l →∀ o:edgeL G,∀ (θ:ℝ≥0),θ ≤1 → ∀ B, Peaks e (r+1) T o u θ B→ Knoxville (grain (fame _) θ) u o (tap (T e (r+1))) (C*B):= by
    choose C hC H using fun a: Loc G 1=> Sable.soak e r u (0,a); let M:=∑ i,C i;refine ⟨M,Finset.sum_nonneg (fun i _=> hC i),fun T hv o θ hb B ht=>?_⟩
    rcases o with ⟨x,i⟩; let U:= Kemp.work (-x) T; have hu:= from_R T l hv (-x)
    have hk: Peaks e (r+1) U (0,i) u θ B:= by
       have he: Lotus.tint (-x) (x,i)=(0,i):= Prod.ext (by simp) (by simp)
       refine ⟨ht.1,fun j hj r hr hp=>?_⟩; rw [←he]; exact fleeing (-x) (ht.2 j hj r hr hp)
    have hh := fled x i (H i U (honor hu) (hu.committees e _) θ hb B hk.1 hk.2)
    have hz: carries x (tap (U e (r+1)))=tap (T e (r+1)):=by change carries x (tap (Kemp.carries (-x) (T e (r+1))))=_; rw [Grail.tap_shift]; funext v; unfold Kemp.carries jetty; rw [show Lotus.tint (- -x) ∘ Lotus.tint (-x) ∘ v=v from funext fun j=>Prod.ext (by simp) (by simp)]
    rw [hz] at hh; exact hh.mono (mul_le_mul_of_nonneg_right (show C i≤ M from Finset.single_le_sum (fun i _=> hC i) (Finset.mem_univ i)) ht.1)
lemma program (r e u l:ℕ)(G:Gauge)(K:KernelChoices)(hs:0<η)(hc:0≤C):∃ A:ℝ,0≤ A∧∀ P:Patch,A≤ (P.L.val:ℝ) → ∀ V:Lodge P,∃ B:ℝ,0≤B ∧∀ (F:Flight j t) (U:Lodge F.patch),∀ h:F.patch=P,h ▸ U=V → RepeatPrices K.penalty η C F→ Perusal K F U u l e (r+1) G (Dove.Mulct F.L) B:= by
    let n:= r+1; have hm:0<n:=by unfold n;omega
    let A:= Real.exp ((u:ℝ)*plum 1 8)* (sack u η*(Fintype.card (Loc G 1)* C))^n
    refine ⟨A^2,sq_nonneg _,fun P hp V=>?_⟩; obtain ⟨B,hB,H⟩:= Lodge.bothPay G K V η hs; obtain ⟨M,hM,h⟩:= soak_hot u e r l G
    let X := (Fintype.card (Bank.Board G P):ℝ) * (1*(Fintype.card (BoardL G P V)*(1*max 1 (B*C)))); let β:=max C (max (B*C) X); have hv:0 ≤ β:=hc.trans (le_max_left ..); have he:=sack_pos u hs
    let N:ℝ:= n*(Real.exp ((u:ℝ)*plum 1 8)*(sack u η*(Fintype.card (Loc G 1)*(β+β)))^n * M)
    refine ⟨N,by unfold N; positivity, fun F U p hz hF=>?_⟩;subst P;subst V
    have ht : (Flight.duo K.penalty F).A0.strip η (C*(F.L.val:ℝ)⁻¹):= by have he:=(hF [] (Nat.zero_le _)).1;simp only [advanceC,List.length_nil, Nat.add_zero,pow_one, div_eq_mul_inv] at he; exact he
    have hh : (Flight.duo K.penalty F).A0.strip η C:= strip_mono ht le_rfl (mul_le_of_le_one_right hc (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr F.L.pos))); obtain ⟨hk,hv,-⟩:= H _ _ hc hh
    refine ⟨fun T hT κ o ε θ hz hp' H W D hW he=>?_⟩
    obtain ⟨σ,Y,hσ,hY⟩:= hT.health o e (r+1)
    let X:=T e (r+1); have ht':∀ k:ℕ,∀ w:r+1=k+1, Knoxville (grain (fame _) θ) u o (tap (lengthen w X)) (M*D):= by intro k hk; cases Nat.add_right_cancel hk; exact h T hT _ θ hp' _ he
    have hv':= absolution o F U κ hs H hz hY hσ (hT.committees _ _) ht' hh hc hk hv; have H:= hv'.add (groove F κ o ht hs hc hm hz H hW); rw [sub_add_cancel] at H;apply H.mono; rw [add_comm]; apply add_le_add; exact mul_le_mul_of_nonneg_right (Dove.adhere hp) hW.1; unfold N n; apply le_of_eq;change (r+1:ℕ)*(Real.exp _ * (M*D)*(sack u η*(Fintype.card _*(β+β)))^(r+1))= _;ring
lemma hill_rests (u R E:ℕ)(G:Gauge)(K:KernelChoices)(hj:4≤j) (ht:4≤t):∃ D:ℝ,0≤ D ∧∀ P:Patch,D≤(P.L.val:ℝ) → ∀ V:Lodge P,∃ B:ℝ, Hearth K P V u R E j t G B:= by
    obtain ⟨η,C,hσ,hC,W,-⟩:= may_use G K j t hj ht
    let I:= Fin (R+E+1)× Fin (R+1) × Fin (E+1)
    choose! D hD H using fun i:I=> program (j:=j) (t:=t) i.1.val i.2.2.val u i.2.1.val G K hσ hC.le
    let M:=∑ i,D i; refine ⟨M, Finset.sum_nonneg (fun i _=> hD i),fun P hp V=>?_⟩
    choose! B hB H' using fun i=> H i P ((show D i ≤ M from Finset.single_le_sum (fun i _=> hD i) (Finset.mem_univ i)).trans hp) V
    let N:=∑ i,B i; refine ⟨N,Finset.sum_nonneg (fun i _=>hB i),fun r hr h l hl e he F U p hz=>?_⟩; cases r with
    | zero=> omega
    | succ n=> let i:I:=(⟨n,by omega⟩,⟨l,by omega⟩,⟨e,by omega⟩); exact review_mono (H' i F U p hz (W F)) (show B i≤ N from Finset.single_le_sum (fun i _=> hB i) (Finset.mem_univ i))
end YM.FormalBulk08.Sierra
