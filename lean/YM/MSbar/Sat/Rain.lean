import YM.MSbar.Sat.Latch
import YM.MSbar.Sat.Ice
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson Tree Pressure Precision Matrix Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {n : Side} {ι τ : Type} [Fintype ι] [Fintype τ]{a C r D ρ m R X: ℝ}{N K : ℕ}
    {l : ι ⊕ τ → Site n}{f : Positions (ι⊕τ) → ℝ}
variable {x : Positions ι}{v w: Positions τ}
lemma stream (ha:0<r)(hb:1 ≤ N)(hC:0≤ C)(h : ∀ p∈ball 0 r,ContDiffAt ℝ ω f p∧ Scatter l a N f p C)(hp:‖meetVar x v‖ ≤ D)(hv:‖w‖≤X)(ht:D+X<r): |f (meetVar x (v+w))-f (meetVar x v)| ≤ wash w*C:=by
    let F(y:ℝ):= meetVar x (v+y • w); have he y (hz:y∈Icc (0:ℝ) 1): F y∈ ball 0 r := by
        rw [mem_ball,dist_zero_right]; apply lt_of_le_of_lt _ ht; unfold F; rw [norm_meet]; rw [norm_meet, max_le_iff] at hp; apply max_le (le_trans hp.1 (le_add_of_nonneg_right ((norm_nonneg _).trans hv)))
        exact (norm_add_le ..).trans (add_le_add hp.2 (by rw [norm_smul]; exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (by simpa [Real.norm_of_nonneg hz.1] using hz.2)) hv))
    have ht:blush w 0=0:=by simp [blush]
    suffices H: |f (meetVar x (v+w))-f (meetVar x v)-blush w 0|≤ wash w*C by rwa [ht,sub_zero] at H
    refine drift f x 0 v w (fun y hv=>(h _ (he y hv)).1) (fun y hy=>?_ ); rw [ht,sub_zero]; letI : DecidableEq τ:=Classical.decEq _
    apply (washes ..).trans; refine mul_le_mul_of_nonneg_left ?_ (wash_nonneg w)
    exact (pi_norm_le_iff_of_nonneg hC).2 (fun j=> by simpa only [Slope, spanSites,Fin.sum_univ_one,separation_self, Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using (h _ (he y hy)).2 _ hb ![Sum.inr j] 0)
end YM.Push.Uniform
namespace YM.MSbar.Heath
open Lattice Wilson Tree Pressure Precision Matrix Filter Function Set Metric RG Push.Uniform
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {c f:Side} {S: StepData c f} {t : S.Choices}{R: Rep G f}
variable (F : Forest S.ratio) (i:S.Choices)
    {σ C δ T A B D d E Y W : ℝ}{h j k N m:ℕ}
-- buy arbitrary order for response paths, actual prices same ledger, phase not chosen
structure Palisade where
    a : ℝ
    density : ℝ -- Scatter
    delta : ℝ -- radius
    initial : ℝ -- smaller ballot radius
    gap : ℝ
    coords : ℕ
    noise : ℝ
    costs : 0 < noise
    first : 0 < initial
    enroll : initial ≤ delta
-- Prop explicit all V matching
structure Grants (t : S.Choices) (R: Rep G f) (F : Forest S.ratio) (p:Palisade) (j:ℕ):Prop where
    buys : Receipt (address F G) p.a j p.coords p.density p.delta p.gap (priced F t R.clip R.path)
    weighs : let f y:= noiseTaylor S (outer G F y) (fine G F y) t; ∀ x∈ball 0 p.delta, ContDiffAt ℝ ω f x ∧ Scatter (address F G) p.a j f x p.noise
    choice x : x∈ball 0 p.delta → ∀ u:S.Choices,noiseTaylor S (outer G F x) (fine G F x) t=noiseTaylor S (outer G F x) (fine G F x) u
    enrollment x:x∈ball 0 p.initial→ uniformed S (fine G F x)
-- availability choose density µ with P named.norm supply Use Before all.
variable (hp:Patch)(K:KernelChoices)
lemma tickets (G:Gauge) (clip:Clip) (hx:0<σ) (C:ℝ) (hj:3≤j) (he:hp.Branches K G) : ∃ p:Palisade, ∀ {c f} {S:StepData c f}, S.patch=hp → S.kernel=K → ∀ (F: Forest S.ratio) (t:S.Choices) (Λ:ℝ)(R:Rep G f), R.clip=clip→ R.path.Bounds clip σ C Λ → Bid.Larger (G:=G) S→ Grants t R F p j :=by
    obtain ⟨Q⟩:= pre_order G σ C hp.J K hj; let A:=Q.tables clip hp
    let m:= |K.penalty| *(noiseEntry G j Q.Z Q.lc Q.W σ hp * (Fintype.card Axis:ℝ) * countCost (entryWidth j hp.L σ/2))
    let Z:=1+|m|; have hZ:0<Z:=by unfold Z; linarith only [abs_nonneg m]
    obtain ⟨r,d,hr,H⟩:= ConnectedActivityE6.Forward.approves hp K he (δ:=1) zero_lt_one
    obtain ⟨J,hJ⟩:= vocals G
    let u:= min (J.r/(shade G)) (r/(2*(J.C*(shade G)))); -- (shade G)=shade G

    by_cases hb: 0 < A.initial
    · refine ⟨⟨A.width,A.value,A.initial,min A.initial u,A.gap,A.coords,Z,hZ,lt_min hb ?_,min_le_left ..⟩,?_⟩
      · have hi:0 < J.C:=zero_lt_one.trans_le hJ.cost
        have hw := shade_pos G; exact lt_min (div_pos hJ.depth hw) (div_pos hr (by positivity))
      intro c f S hx' ht F t Λ R hl hW hL
      -- buy.L> pm; replace in subproof
      have hp:= (Q.receipt F t (R:=R.path) hW hL (congr_arg Patch.J hx') ht); rw [hx'] at hp
      refine ⟨?_,?_,?_,?_⟩
      · rw [hl]; exact hp.1
      · have hg:= penalized F t hL.1 j ((by norm_num:2≤3).trans hj) Q.labels Q.exp Q.log Q.focus hx
        intro f x hX; apply And.imp (a:=ContDiffAt ℝ ω f x) (b:=Scatter (address F G) A.width j f x m) (fun h=>h) (fun h=> h.mono ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)))
        have hz : ContDiffAt ℝ ω f x∧ Scatter (address F G) (weaker j (entryWidth j S.patch.L σ)) j f x
            (|S.kernel.penalty| * (noiseEntry G j Q.Z Q.lc Q.W σ S.patch *(Fintype.card Axis:ℝ)*countCost (entryWidth j S.patch.L σ /2))) := hg x (show x ∈_ from by rw [ht,hx']; exact hX)
        rw [ht,hx'] at hz; exact hz
      · intro x hx t'; let a:=mainTerm clip R.path (fine G F x); exact add_left_cancel (show a+ _=a+ _ from (hp.2 x hx t').symm)
      intro z hz; change z∈ball _ (min A.initial u) at hz; rw [mem_ball,dist_zero_right] at hz
      let w:=(shade G)*‖z‖; have hw : w ≤ J.r:=by
         unfold w; rw [mul_comm]; exact (le_div_iff₀ (shade_pos G)).1 (hz.le.trans ((min_le_right ..).trans (min_le_left ..)))
      have hζ: 2*(J.C*w) ≤ r:=by
         have hi:0 < J.C:=zero_lt_one.trans_le hJ.cost; have hu:=mul_pos zero_lt_two (mul_pos hi (shade_pos G)); have hh:= (le_div_iff₀ hu).mp (hz.le.trans ((min_le_right ..).trans (min_le_right ..))); unfold w; linarith only [hh]
      let p:=partSpace (Primary c G) (Key F G) z; let y:=p.1; let x:=p.2; have ha: z= meetVar y x:= by unfold y x p meetVar; exact ((partSpace ..).symm_apply_apply z).symm
      have hc : ‖y‖ ≤ ‖z‖ ∧ ‖x‖≤‖z‖:= by have ht := norm_meet y x; rw [← ha] at ht; rw [ht]; exact ⟨le_max_left _ _,le_max_right _ _⟩ -- edit
      let U:=outer G F z; have hV: U=represent (tint G _ y):=by unfold U outer; rw [ha,paint_meet]
      have hC:0 ≤ J.C:=zero_le_one.trans hJ.cost
      have hE (x:G.Color) (hv: ‖x‖≤ w): G.chord (G.lieExp x) ≤ J.C*w:= (hJ.small x (hv.trans hw)).2.trans (mul_le_mul_of_nonneg_left hv hC)
      have ht (i:Edge (Site c)): G.chord (U i) ≤ J.C*w:=by
          rw [hV]; unfold represent RG.increment; simp only [Pi.one_apply,mul_one]; exact hE _ ((norm_le_pi_norm (tint G _ y) (i.1, Exterior.coord i.2)).trans ((tint_le y).trans (mul_le_mul_of_nonneg_left hc.1 (shade_pos G|>.le))))
      -- rename ht collision kernel
      have hk(i:Edge (Site f)): G.chord (fine G F z i) ≤ r :=by
          have he₀: fine G F z=lifting F U (tint G _ x):=by unfold fine; congr 1
          rw [he₀]; by_cases hi:i∈F.trunks; rw [show lifting F U (tint G _ x) i=1 from F.on_tree _ ⟨i,hi⟩, G.chord_one]; exact hr.le
          let k:F.Free:=⟨i,hi⟩; unfold lifting; rw [show i= k.val from rfl] -- rw may cancel
          rw [F.off_tree]; have h : G.chord (Precision.replica S.ratio U i)≤ J.C*w:=by unfold Precision.replica; split; rw [G.chord_one]; exact mul_nonneg hC (mul_nonneg (shade_pos G|>.le) (norm_nonneg _)); exact ht _
          exact (G.chord_triangle ..).trans (le_trans (add_le_add (hE _ ((norm_le_pi_norm (tint G _ x) k).trans ((tint_le x).trans (mul_le_mul_of_nonneg_left hc.2 (shade_pos G|>.le))))) h) (by linarith only [hζ]))
      intro i; have hp j := H c f S hx' ‹S.kernel=K› (fine G F z) i j (fun t _=>hk t); exact ⟨fun j=>(hp j).1,fun j=> (hp j.1|>.2 j.2).2⟩
    -- initial positivity needed independent of any S!
    refine ⟨⟨0,0,1,1,0,0,1,one_pos,one_pos,le_rfl⟩,fun hx ht F t Λ R hl hW hL=>?_⟩; have he := Q.receipt F t hW hL (congr_arg Patch.J hx) ht -- binders likely
    rw [hx] at he; exact (hb he.1.pos_r).elim
end YM.MSbar.Heath
