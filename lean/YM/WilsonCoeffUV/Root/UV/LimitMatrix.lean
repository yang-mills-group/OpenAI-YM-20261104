import YM.WilsonCoeffUV.Root.UV.LimitHeat
/-!
# Mixed step closure limit convergence (quantifying at fixed level); quantitative uniformity on entries provided separately. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α β:Type*}{r h D l e j k a N M m b i q:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C x y δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}{θ:ℕ→ℝ}
lemma lastTw [NormedAddCommGroup U]{P:ℕ→U}{V:U}(p:Tendsto P atTop (𝓝 V))(h:∀ b≥m,∀ N M,b≤N → b≤ M → twain A (θ b) (P N) (P M))(b)(v:m≤ b)(hq:b≤N): twain A (θ b) (P N) V:=by
    refine ⟨(h b v N N hq hq).main, le_of_tendsto p.norm ?_, le_of_tendsto (tendsto_const_nhds.sub p).norm ?_⟩
    · exact (eventually_ge_atTop b).mono fun n hn=> (h b v n n hn hn).main
    exact (eventually_ge_atTop b).mono fun n hn=> (h b v N n hq hn).gap
lemma minting (R:Realm G e E)(h:R.anchor≤m)(v:i≤e)(a b): ∃ B:ℝ,∀ᶠ N in atTop, twain B (R.ωJ m N) (coeff i ((ratioHigh R.draws R.paid N m)^a*((ratioHigh R.draws R.paid N m)⁻¹)^b)) (coeff i ((back (viridian R.draws R.paid m))^a*((back (viridian R.draws R.paid m))⁻¹)^b)):=by
    let C j (p:j≤ i):Credit:= (pitch_step G e E j (p.trans v)).choose
    let P (j:ℕ):ℝ:= if p:j≤ i then R.cash (C j p) m else 1; let S:= Finset.range (i+1)
    have hx j (p:j∈ S): 1≤P j:= by unfold P; rw [dif_pos (show j≤ i from Nat.le_of_lt_succ (Finset.mem_range.mp p))]; exact Credit.purchase _ (R.depth m h)
    let A:= 1+∑ j∈S,P j; have hA:1≤ A:= le_add_of_nonneg_right (Finset.sum_nonneg fun i hi=> zero_le_one.trans (hx i hi))
    have hs (N:ℕ)(p:m<N)(j:ℕ)(hp:j≤ i) : twain A (R.ωJ m N) (coeff j (pitch R.draws R.paid N m)) (coeff j (viridian R.draws R.paid m)) := by
       have ht:= lastTw (m:=m+1) (show Tendsto (fun N=>coeff j (pitch R.draws R.paid N m)) _ _ from evergreen R h (hp.trans v)) (θ:=R.tempC m) (fun b hb n M p q=> (pitch_step G e E j (hp.trans v)).choose_spec R m h b n M hb p q) N p le_rfl
       have hh : R.cash (C j hp) m ≤ A:= by
          rw [← show P j=R.cash (C j hp) m from dif_pos hp]; exact (Finset.single_le_sum (fun i hi=> zero_le_one.trans (hx i hi)) (show j∈ S from Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)
       exact (ht.lift hh (trail_pos ..).le).wide (le_mul_of_one_le_left (trail_pos ..).le (Credit.purchase _ (R.depth _ h)))
    obtain ⟨n,C,h,g⟩:= scalar_receipt i a b
    refine ⟨C*A^n,(eventually_gt_atTop m).mono fun N hx=>?_⟩
    exact g ⟨A,R.ωJ m N,hA,R.ωJ_nn (by assumption) N,pitch R.draws R.paid N m,viridian R.draws R.paid m, angle_tilt R.hG R.green hx,one_sun R (by assumption),hs N hx⟩

variable (L:Theatre H T p e E W)
-- independent history. define for consumer irrespective limit realm
abbrev Grey (A:Levels G)(Ñ:ChartRatio G)(m:ℕ)(P:Thesis F D): Thesis F D:= fun i=> Blue.mix (back (viridian A Ñ m)) (chorus (loose A m) A.clock.kernel Ñ (holdΓ A m) (holdM A m) (timeless A Ñ (m+1)) h (P i))
def Hesper (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(v:h<D)(m:ℕ):= Grey A Ñ m (glory A Ñ T v (m+1))
def HesperN (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(N m:ℕ):= (descend A Ñ N m (Peaks A Ñ T p N (m+1))).2
abbrev Theatre.goneC (N m):= HesperN L.V.draws L.V.paid T p N m
abbrev Theatre.gone (m):= Hesper L.V.draws L.V.paid T p m
lemma bake (u:L.V.anchor≤m)(v:i≤ e)(j:Alma F)(r):Fleets (L.V.ωJ m) (L.angle m u).lamp.exitS (fun n=> L.goneC n m j i r) (L.gone m j i r):=by
    let R:= L.V; let V n:= ratioHigh R.draws R.paid n m; let K:= back (viridian R.draws R.paid m)
    change Fleets _ _ (fun n=>Blue.mix (V n) (copper L n m j) i r) (Blue.mix K (Gold L m j) i r); unfold Blue.mix; apply Fleets.fleetSum; intro k hk; have hf:= Finset.mem_range.mp hk
    obtain ⟨A,p⟩:= minting R u (show i-k≤e+1 from by omega) k r; obtain ⟨B,h⟩:= golden (m:=m) L u (show k≤ e from by omega) j r
    exact ⟨_, (p.and h).mono fun n h=> Shelf.mag h.2 h.1⟩
lemma Fleets.echo {P:ℕ→ ChamberTen G (Vote D) r}{Q:ChamberTen G (Vote D) r}(h:Fleets θ s P Q)(v:0<s)(p:Tendsto θ atTop (𝓝 0))(F:Frame G a)(i:Alma F): Tendsto (fun n=>echoS F (P n) i) atTop (𝓝 (echoS F Q i)):=by
    obtain ⟨A,hp⟩:=h; obtain ⟨C,hC,u⟩:= paid_echo F s v r D; apply gleam (a:=C*A) p; refine hp.mono fun n hn=>?_
    exact ⟨u i _ _ hn.wax,u i _ _ hn.wane,by rw [← echo_minus F i hn.wax hn.wane v v,mul_assoc]; exact u i _ _ hn.toll⟩
lemma gleet (F:Frame G h)(P:ℕ→Single G D)(Q:Single G D)(h:∀ i≤k,∀ r,Fleets θ s (fun n=>P n i r) (Q i r))(u:Tendsto θ atTop (𝓝 0))(v:0<s)(i: Alma F): Tendsto (fun n=>glean F (P n) k i) atTop (𝓝 (glean F Q k i)):=by
    simp_rw [glean]; apply tendsto_finsetSum; intro j hj; split <;> rename_i g; exact (h _ (by have hh:= Finset.mem_range.mp hj; omega) _).echo v u F i
    exact tendsto_const_nhds
abbrev Jacob (A: Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(N m:ℕ):=prismata F (HesperN A Ñ T p N m)
abbrev Jacie (A: Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(m:ℕ):=prismata F (Hesper A Ñ T p m)
lemma matrix_glim (u:L.V.anchor≤m)(v:i≤ e)(a b: Alma F): Tendsto (fun n=> lineS (Jacob L.V.draws L.V.paid T p n m) i a b) atTop (𝓝 (lineS (Jacie L.V.draws L.V.paid T p m) i a b)):=by
   simp_rw [Jacob,Jacie, coined]; exact gleet F (fun n=> L.goneC n m b) (L.gone m b) (fun i h=>bake L u (h.trans v) b) (L.V.ωJ_vanish m) (L.angle m u).lamp.positive _
lemma leaseN (u:L.V.anchor≤m)(g:m<N): leaseM (loose L.V.draws m).L F (lineS (Jacob L.V.draws L.V.paid T p N m) 0):= by
    obtain ⟨V,hv⟩:= pickS ((L.V.mint m u).postStand g L.V.hG L.V.green) (L.effort m u).1.symm
    obtain ⟨G⟩:= (L.effort m u).2 _ _ _ _ _ hv; rw [← plumeK L u]; exact (path_warp L.V.draws L.V.paid p g L.V.hG L.V.green H (Peaks L.V.draws L.V.paid T p N (m+1)) (production L (show m+1≤N from g) (by omega)).1 _ _ (L.effort m u).1 V hv G).1
lemma leaseOld (u:L.V.anchor≤m): leaseM (loose L.V.draws m).L F (lineS (Jacie L.V.draws L.V.paid T p m) 0):=⟨fun i j x=> tendsto_nhds_unique (matrix_glim L u (Nat.zero_le e) i j) (tendsto_const_nhds.congr' ((eventually_gt_atTop m).mono fun _n hn=> ((leaseN L u hn).1 _ _ x).symm)), fun i j x v=> tendsto_nhds_unique (matrix_glim L u (Nat.zero_le e) i j) (tendsto_const_nhds.congr' ((eventually_gt_atTop m).mono fun _n hn=> ((leaseN L u hn).2 _ _ x v).symm))⟩
lemma gliding (u:L.V.anchor≤ m)(v:k≤e)(i j): impose (L.matron m) (prismata F (L.gone m)) i k j=L.gone m i k j:=by
    have H n (t:m<n): impose (L.lore n m).2 (prismata F (L.goneC n m)) i k j=L.goneC n m i k j:= by
       unfold Theatre.lore; rw [marched _ _ _ p t]; exact congr_fun (congr_fun (congr_fun (refluent (V:=Cosmos.descend L.V.draws L.V.paid n m (L.lore n (m+1))) (stellarized (leaseN L u t))) _) _) _
    ext1 x; have hv:= (bake L u v i j).point (L.V.ωJ_vanish m) x
    refine tendsto_nhds_unique (f:=fun n=> impose (L.lore n m).2 (prismata F (L.goneC n m)) i k j x) ?_ (hv.congr' ((eventually_gt_atTop m).mono (fun n hn=> congr_fun (H n hn).symm x)))
    simp only [impose, affix,Finset.sum_apply,Pi.smul_apply]; apply tendsto_finsetSum; intro s _; apply tendsto_finsetSum; intro y hy; have he:= Finset.mem_antidiagonal.mp hy; exact (matrix_glim L u (show y.1≤ e from by omega) s i).smul (gleaming L u (show y.2≤ e from by omega) s j x)
end YM.WilsonCoeffUV.Cosmos
