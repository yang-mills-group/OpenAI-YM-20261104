import YM.SchemeConversionRG11.FirstW.Jade.Edge
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function Filter MeasureTheory Set Metric Lattice Pert Align Position Topology Maxwell MvPolynomial
open scoped BigOperators Classical
variable {T: Itinerary} {c:ℕ→Side} {G:Gauge}{r:ℕ}
lemma diameter_q {p:Points r}(h:p∈ conf r) : ∃ R:ℝ, R>0 ∧ ∀ i j:Fin r,i≠j → 8*R<‖p i-p j‖:= by
 have he : ∀ᶠ R in 𝓝[>] (0:ℝ), ∀ i j:Fin r,i≠j→ 8*R<‖p i-p j‖ := eventually_all.mpr fun i=>eventually_all.mpr fun j=> by
   by_cases e:i=j; · exact Eventually.of_forall fun _ k=> False.elim (k e)
   have ht:Tendsto (fun r:ℝ=>8*r) (𝓝[>] (0:ℝ)) (𝓝 0):= by simpa only [mul_zero] using (show Tendsto (fun x=>x) (𝓝[>] (0:ℝ)) (𝓝 0) from tendsto_id.mono_left nhdsWithin_le_nhds).const_mul (8:ℝ) -- lemma
   exact (ht.eventually (gt_mem_nhds (norm_pos_iff.mpr (sub_ne_zero.mpr (h.ne e))))).mono fun _ hi _=>hi
 have hu : ∀ᶠ i in 𝓝[>] (0:ℝ), 0 < i := self_mem_nhdsWithin
 exact (hu.and he).exists
lemma covers_r (F:Labels.Frames G)(hc:MarkGrid T c) : ∃ Z:ℕ→Pack F,∀ Q:Wash,stampB F Z T Q := by
 let Q:Wash := ⟨1,2,zero_lt_one,by norm_num⟩
 obtain ⟨p,hP,h⟩:=performs (fun i=>bondM F T i Q) (mom_paid F hc Q) (kissed hc F Q); exact ⟨p,fun W=>⟨adjust_bath hc Q W (u:=fun j=> glyph F (p j)) hP,h⟩⟩
lemma covers_sub (F:Labels.Frames G)(Z:ℕ→Pack F)(m:ℕ→ℕ)(hs:Tendsto m atTop atTop)(Q:Wash)(h:stampB F Z T Q): stampB F (Z∘m) (Rig.path T m hs) Q := by
 constructor; swap; · intro L; exact (h.2 L).comp hs
 intro k hk q hq; obtain ⟨x,H⟩:= h.1 k hk q hq; exact ⟨_,H.comp hs⟩
lemma d_paid (F:Labels.Frames G){p:Points r}(o:∀ i,Full.Grid (T.period i) r)(hp:Diorama T o p)(hg:G.Simple)(hc:MarkGrid T c)(v:Fin r→E F 6)(Z:ℕ→Pack F)(hz:∀ Q:Wash,stampB F Z T Q) : Helen (showP T F o v Z):=by
 obtain ⟨R,hR,B⟩:= diameter_q hp.ht; let Q:Wash:=⟨R/3,R/2,by linarith,by linarith⟩
 exact whole_at hp F hg v Q (by change R/2<R; linarith) B hc Z (hz _)
-- itinerary generalized Arrives by convergence on all interleaved subsequences
section inter
variable {X W:Type} [TopologicalSpace X][T2Space X][TopologicalSpace W] {E:ℕ→Type*} {K:Set W}{z:W}{p:∀ i,E i→ X}{v:∀ i,E i → W} {n m:ℕ→ℕ}
-- zipper on dependent grid
private lemma fast (n m:ℕ→ℕ) (hn:Tendsto n atTop atTop)(hm:Tendsto m atTop atTop) : Tendsto (fun i:ℕ=> if i%2=0 then n (i/2) else m (i/2)) atTop atTop:= by
 have ht : Tendsto (fun i:ℕ=> i/2) atTop atTop:= tendsto_atTop.2 fun c=> (eventually_ge_atTop (2*c)).mono fun i hi=> by omega
 rw [Filter.tendsto_atTop]; intro i; filter_upwards [(hn.comp ht).eventually (eventually_ge_atTop i),(hm.comp ht).eventually (eventually_ge_atTop i)] with k hk he; split_ifs <;> assumption
private lemma even_cap : Tendsto (fun i:ℕ=>2*i) atTop atTop := tendsto_atTop_mono (f:=id) (fun i=>show i≤2*i by omega) tendsto_id
omit [TopologicalSpace X] [T2Space X] in
private lemma weave_cost (u:∀ i,E (n i))(a:∀ i,E (m i))(hv:Tendsto (fun i=>v (n i) (u i)) atTop (𝓝 z))(he:Tendsto (fun i=>v (m i) (a i)) atTop (𝓝 z)) :
    let S(i:ℕ):= if i%2=0 then n (i/2) else m (i/2)
    ∃ w:∀ i,E (S i), Tendsto (fun i=>v (S i) (w i)) atTop (𝓝 z) ∧ (∀ i,p (S (2*i)) (w (2*i))=p (n i) (u i)) ∧ (∀ i,p (S (2*i+1)) (w (2*i+1))=p (m i) (a i)):= by
 intro S; let w(i:ℕ): E (S i):= if h:i%2=0 then ((show n (i/2)= S i from (if_pos h).symm) ▸ u (i/2)) else ((show m (i/2)= S i from (if_neg h).symm) ▸ a (i/2))
 have hs(Q:Type)(f:∀ i,E i→Q)(i:ℕ): f (S i) (w i)=if i%2=0 then f (n (i/2)) (u (i/2)) else f (m (i/2)) (a (i/2)) := by
   have echo {i j:ℕ}(x:E i)(h:i=j): f j (h ▸ x)=f i x:= by subst j; rfl
   unfold w; by_cases h:i%2=0; · rw [dif_pos h]; exact (echo ..).trans (if_pos h).symm
   rw [dif_neg h]; exact (echo ..).trans (if_neg h).symm
 refine ⟨w,?_,fun i=>by rw [hs _ p,if_pos (show 2*i%2=0 by omega),show 2*i/2=i by omega],fun i=>by rw [hs _ p,if_neg (by omega), show (2*i+1)/2=i by omega]⟩ -- universe!
 have ht : Tendsto (fun i:ℕ=> i/2) atTop atTop:= tendsto_atTop.2 fun c=> (eventually_ge_atTop (2*c)).mono fun i hi=> by omega
 refine tendsto_def.mpr fun s hz=>?_
 filter_upwards [(hv.comp ht).eventually (p:=fun x=>x∈s) hz,(he.comp ht).eventually (p:=fun x=>x∈s) hz] with i hi hp
 change v (S i) (w i) ∈ s; rw [hs _ v]; split_ifs <;> assumption
lemma transit (h:∀ (m:ℕ→ℕ),Tendsto m atTop atTop→∀ u:∀ i,E (m i), Tendsto (fun i=>v (m i) (u i)) atTop (𝓝 z) → Helen (fun i=>p (m i) (u i))) (hs:Tendsto n atTop atTop)(q:∀ i,E (n i))(hq:Tendsto (fun i=>v (n i) (q i)) atTop (𝓝 z)) : ∃ V:X,∀ m:ℕ→ℕ,Tendsto m atTop atTop→∀ u:∀ i,E (m i),Tendsto (fun i=>v (m i) (u i)) atTop (𝓝 z) → Tendsto (fun i=>p (m i) (u i)) atTop (𝓝 V) := by
 obtain ⟨V,H⟩:= h n hs q hq; refine ⟨V,?_⟩
 intro m hm u hu; let M(i:ℕ):= if i%2=0 then n (i/2) else m (i/2)
 obtain ⟨w,hp,h₁,h₂⟩:= weave_cost (p:=p) q u hq hu; obtain ⟨W,hW⟩:= h M (fast n m hs hm) w hp
 have hw:= (hW.comp even_cap).congr h₁; rw [tendsto_nhds_unique H hw]; apply Tendsto.congr h₂ (hW.comp (tendsto_atTop_mono (f:=fun i=>2*i) (fun i=> show 2*i≤2*i+1 by omega) even_cap))
end inter
end YM.RG11.FirstW.Deck
