import YM.OPE.Compatible.Scrape.Reef
/-!
# Uniform wedge at recovery
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Next.Rank Next.Rank.Spindle Source WilsonStartup Gauge Next.Fluctuations Metric
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X:Type*}{n:Side}(o:Site n){b i k r m:ℕ}
structure Pad (G:Gauge) where
       (r:ℝ) -- edit
       (L B:ℝ)
       pos : 0<r
       hL : 0<L
       hB :0<B
       budget : L*r≤1/4
       analytic x:‖x‖≤r → ContDiffAt ℝ ω (undo G) x
       turns x: ‖x‖≤r → G.chord (recover G x)≤ L*‖x‖
       rotates x: ‖x‖≤r→∀ u:G.El,recover G (G.adjoint u x)= u * recover G x*u⁻¹
       solves u: G.chord u≤B → recover G (G.curvature u)=u
       small x:‖x‖≤r → ‖undo G x‖≤1
lemma curtainL (G:Gauge): Nonempty (Pad G):=by
       obtain ⟨U,hu,ht⟩:= nhds_basis_closedBall.eventually_iff.1 (recover_left G); let H:=U/G.colorScale; have hz:=G.colorScale_pos; have hU:0<H:= div_pos hu hz; have hp(u:G.El)(h:G.chord u≤H):recover G (G.curvature u)=u:=by
            refine ht (mem_closedBall.mpr ?_); change dist (G.mat u) (1:G.Mat)≤_; rw [dist_eq_norm, ←chord_dist, mul_comm]; exact (le_div_iff₀ hz).mp h
       obtain ⟨D,t,hD,ht,h⟩:=chart_linear_cost (fun a=>G.mat (recover G a)) 0 (recover_analytic G).analyticAt; let L:=D/G.colorScale; have hl:0<L:=div_pos hD hz; have hV(a:G.Color)(hc:‖a‖≤t): G.chord (recover G a)≤ L*‖a‖:=by
            apply le_of_mul_le_mul_left _ hz;rw [chord_dist, ← mul_assoc,show G.colorScale*L=D from by unfold L; field_simp]
            simpa only [recover_zero,Gauge.mat_one,sub_zero] using h a (by rwa [sub_zero])
       obtain ⟨r',hr,HQ⟩:=nhds_basis_closedBall.eventually_iff.1 ((undo_analytic G|>.eventually (by simp)).and ((recover_right G).and ((undo_analytic G|>.continuousAt.norm.tendsto).eventually (ge_mem_nhds (by simp: ‖undo G 0‖<1)))))
       let r:=min (min t r') (min (H/L) (1/4/L))
       have ha:r≤t:= (min_le_left ..).trans (min_le_left ..); have hq(x:G.Color)(h:‖x‖≤r):=HQ (mem_closedBall.mpr (show dist x 0≤r' from by rw [dist_zero_right]; exact h.trans ((min_le_left ..).trans (min_le_right ..))))
       have hy: L*r≤H:= (mul_comm ..).trans_le ((le_div_iff₀ hl).mp ((min_le_right ..).trans (min_le_left ..))); refine ⟨⟨r,L,H,lt_min (lt_min ht hr) (lt_min (div_pos hU hl) (div_pos (by norm_num) hl)),hl,hU,(mul_comm ..).trans_le ((le_div_iff₀ hl).mp ((min_le_right ..).trans (min_le_right ..))),fun x hx=> (hq x hx).1, fun x hx=> hV x (hx.trans ha),fun x hx u=>?_, hp, fun x hx=>(hq x hx).2.2⟩⟩; let V:=recover G x; calc
            _=recover G (G.curvature (u*V*u⁻¹)):= (by rw [G.curvature_conjugate,show G.curvature V=x from (hq x hx).2.1])
            _=_ :=hp _ (by rw[G.chord_conj]; exact (hV x (hx.trans ha)).trans ((mul_le_mul_of_nonneg_left hx hl.le).trans hy))
       -- edit
noncomputable def offsetDir (o: Site n) (h:2*(b+1)<n.val) (e:Edge (Site n)): DrawerB G b→L[ℝ] G.Color:= if he:e∈Room o b then ContinuousLinearMap.proj (register h ⟨e,he⟩) else 0
abbrev WingB (h:2*(b+1)<n.val):DrawerB G b→L[ℝ] (Directions G n):=ContinuousLinearMap.pi (fun i=>offsetDir o h i)
lemma sizeTD (e:Edge (Site n))(h:2*(b+1)<n.val)(x:DrawerB G b): ‖offsetDir o h e x‖≤‖x‖:=by unfold offsetDir; split; rename_i hP; exact norm_le_pi_norm x (register h ⟨e,hP⟩); simp
abbrev Steer (h:2*(b+1)<n.val)(x:DrawerB G b):Directions G n:=fun i=>undo G (WingB o h x i)
abbrev motorB (h:2*(b+1)<n.val)(x:DrawerB G b):Config G n:=increment 1 (Steer o h x)
lemma cssh (h:2*(b+1)<n.val)(x:DrawerB G b)(i:Edge (Site n)): motorB o h x i=recover G (WingB o h x i):=mul_one _
variable {C p:ℝ}
section
variable (P:Pad G) {U:Support n}
lemma fris (h:2*(b+1)<n.val){x:DrawerB G b}(hz:‖x‖ ≤ P.r): ContDiffAt ℝ ω (Steer (G:=G) o h) x:= contDiffAt_pi.mpr fun i=> (P.analytic _ ((sizeTD o i h x).trans hz)).comp (f:=offsetDir o h i) x (offsetDir o h i|>.contDiff.contDiffAt)
lemma mainR (h:2*(b+1)<n.val){t:ℝ}(ht:0 ≤ t)(hx:t ≤ 1){x:DrawerB G b}(hp:‖x‖≤ P.r): flags t (motorB o h (t • x))=∅:=by
       let W:=motorB o h (t • x); have hd (i:Edge (Site n)): ‖offsetDir o h i (t • x)‖≤t*P.r:= (sizeTD o i h _).trans ((norm_smul_of_nonneg ht _).trans_le (mul_le_mul_of_nonneg_left hp ht)); have he(i):G.chord (W i)≤ t/4:=by
           rw [show W i=recover G (offsetDir o h i (t • x)) from cssh ..]; apply (P.turns _ ((hd i).trans (mul_le_of_le_one_left P.pos.le hx))).trans; calc
                  _ ≤ P.L*(t*P.r):=mul_le_mul_of_nonneg_left (hd i) P.hL.le
                  _ ≤ _:=by rw[mul_left_comm,div_eq_mul_inv];exact mul_le_mul_of_nonneg_left (by simpa only[one_div] using P.budget) ht
       apply Finset.eq_empty_of_forall_notMem; intro i hi; obtain ⟨j,hj,hL⟩:= (flags_spec ..).1 hi; have hh:= travel_chord W (square j.2.val.1 j.2.val.2) j.1 _ he; change t < G.chord (travel W j.1 _) at hL; rw [show ((square j.2.val.1 j.2.val.2).length:ℝ)=4 from by simp [square]] at hh; linarith only [hh,hL]
end
end YM.OPE.Spells
