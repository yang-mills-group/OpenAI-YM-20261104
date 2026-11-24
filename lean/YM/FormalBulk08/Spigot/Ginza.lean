import YM.FormalBulk08.Spigot.Wires
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}


open Stationary hiding Rays shine
open Work.F03 Work.F05
open scoped Matrix.Norms.Frobenius

def Glare (p:Pap (wire G n))(E:ℕ):Prop:= ∀ (I:Type)[Fintype I] (a b : Jets.Rays I → Jets.Rays (wire G n))(k: Jets.Rays I → Site n→G.El), a 0=0 → b 0=0 → ContDiffAt ℝ ω a 0 → ContDiffAt ℝ ω b 0 → Army k 0 → (∃ g:G.El,k 0=fun _=> g) → (∀ᶠ z in 𝓝 0,input G n (b z)=Lattice.gauge (k z) (pull 1 0 (input G n (a z)))) → Through E (roam ℝ (motor a) p) (roam ℝ (motor b) p)

section
variable (i: hue G)(x:Site n)
lemma ledge (p : Pap (wire G n)) (h : Glare p E) (hp : ∀ v,step v≠(0:Site n)) : Through E (roam ℝ (motor (deltaS i x)) p) (PowerSeries.map (MvPolynomial.rename (Sum.inl : wire G n→ dah (wire G n))).toRingHom p) := by
   rw [←fit_translate]; symm
   exact h (dah (wire G n)) (cheekL (wire G n)) (deltaS i x) (glow i x) (map_zero _) (delta_home ..) ((cheekL (wire G n)).contDiff.contDiffAt) (delta_cap ..) (glow_cap i x) ⟨1,by ext b;simp [glow]⟩ (by filter_upwards [eventually_all.mpr fun v:Site n × Axis=>post_delta i x v.2 v.1 i (hp _)] with z hz; rw [pull_id]; exact funext hz)
lemma drummond (p:Pap (wire G n)) (h : Glare p E) (hp : ∀ v,step v≠(0:Site n)) : Through E (∑ v : wire G n,yaw v p*((if v.1=x then spinP i v true else 0)+(if v.1+step (axisEquiv.symm v.2.1)=x then spinP i v false else 0))) 0 := by
   have he : Through E (curly _ (roam ℝ (motor (deltaS i x)) p)) 0 := by
      intro j hj
      have H := (show Through E (curly _ (roam ℝ (motor (deltaS i x)) p)) (curly _ _) from beam_through _ (ledge i x p h hp)); rw [H j hj]; rw [curly,coeff_shaft,map_zero,coeff_map]; generalize coeff j p=U;change MvPolynomial.pderiv (R:=ℝ) (.inr () : dah (wire G n)) (MvPolynomial.rename Sum.inl U)=0
      induction U using MvPolynomial.induction_on <;> simp_all
   have hh : Through E (shortL (wire G n) (curly _ (roam ℝ (motor (deltaS i x)) p))) (shortL _ 0):= Through.change_congr _ he
   rw [map_zero] at hh; refine (Eq.mp ?_ hh); congr 1; symm
   unfold curly roam;rw [diff_chain,map_sum]; apply Finset.sum_congr rfl; intro a _; rw [map_mul]
   obtain ⟨h₁,h₂⟩:=drying i a x hp; rw [←h₂]; congr 1
   change _ = roam ℝ _ (roam ℝ _ (yaw a p))
   rw [roam_compose,show (fun v=>shortL _ (motor (deltaS i x) v))=_ from funext (fun b=> (drying i b x hp).1),virgin]
lemma highRoad (p : Pap (wire G n)) (h : Glare p E) (hp : ∀ v,step v≠(0:Site n)) :
   Through E (∑ v: TypeFace 1 × hue G,(driftP i p true (x,v)+driftP i p false (backwards x v.1,v))) 0:= by
   intro e he; rw [←drummond i x p h hp e he]; congr 1; rw [Finset.sum_add_distrib];simp_rw [mul_add, Finset.sum_add_distrib];congr 1
   · symm;rw [Fintype.sum_prod_type, Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
     rw [Finset.sum_eq_single x]; exact (by rw [if_pos rfl];rfl); intro b _ hb; rw [if_neg hb,mul_zero];simp
   symm;rw [Fintype.sum_prod_type, Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
   rw [Finset.sum_eq_single (backwards x j.1)]; exact (by simp [backwards,driftP]); swap; · simp
   intro b _ hb; rw [if_neg (fun he=> hb (eq_sub_of_add_eq he)),mul_zero]

lemma hillSong(e r:ℕ)(p : Pap (wire G n)) (h:Glare p E)(he:e≤ E) (hp:∀ v,step v≠(0:Site n)) : ∑ a∈Finset.antidiagonal e,cruisesD i x a r (rancho p)=0 := by
    have he:= congr_arg (canyon (V:=wire G n) r) (highRoad i x p h hp e he)
    simp only [map_sum,map_zero,map_add,driftP,coeff_mul,canyon_eq,rank_grade] at he; rw [←he]; unfold cruisesD; rw [Finset.sum_comm]; simp_rw [Finset.sum_add_distrib]
end
lemma leadTap (i:hue G) (x : Cover) (e r : ℕ) (U : Pot G) (S : (n:Side)→Pap (wire G n)) (h : ∀ e r,0<r → Light (U e r) (fun n=> rancho (S n) e r)) (hp : ∀ᶠ n in atTop,Glare (S n) E) (hh:e≤ E) :
    ∑ a∈Finset.antidiagonal e,cruisesD i x a r U=0:= by
    have hj : Light (∑ a∈Finset.antidiagonal e,cruisesD i x a r U) (fun n=> ∑ a∈Finset.antidiagonal e,cruisesD i (wrap n x) a r (rancho (S n))) := by
        apply ideas;intro j _;unfold cruisesD; apply ideas; intro v _;have hh (n : Side) : (backwards (wrap n x) v.1,v)=Lotus.drip n (backwards x v.1,v):= by simp only [backwards,Lotus.drip,map_sub,wrap_step] --
        simp_rw [hh];exact fun a=> (steer_shape i h (x,v) true j r a).add (steer_shape i h (backwards x v.1,v) false j r a)
    have hv(v:Axis) : ∀ᶠ n : Side in atTop, step v ≠ (0:Site n) := by
       filter_upwards [effect (step v),effect 0] with n hn hm H; rw [map_zero] at hm; rw [wrap_step,H,hm] at hn; have hp:=congr_fun hn v;simp at hp
    exact funext fun a=> tendsto_nhds_unique (hj a) (tendsto_const_nhds.congr' (by filter_upwards [hp,eventually_all.mpr hv] with n hn hp; rw [hillSong _ _ _ _ _ hn hh hp]; rfl))

lemma luster (g:G.El) (p:Pap (wire G n))(h:Glare p E)(e r:ℕ)(hf:e≤ E): rancho p e r=pearl (pointL g n) (rancho p e r):= by
   let R:=armature g n
   have hp (x) : Stationary.input G n (R x) = Lattice.gauge (fun _=>g) (pull 1 0 (Stationary.input G n x)) := by
      funext b; rw [pull_id,Lattice.gauge,Stationary.input,represent_link,Stationary.input,represent_link]; unfold R; rw [City.seated];apply G.mat_injective; simp [Gauge.conjugate]; exact G.exp_conjugate g _
   have he := h (wire G n) (fun z:Jets.Rays (wire G n)=>z ∘ id) R (fun _ _=>g) rfl (map_zero R) contDiffAt_id R.contDiff.contDiffAt (fun _=>contDiffAt_const) ⟨g,rfl⟩ (.of_forall hp) e hf
   rw [Bank.pane_letter (pointL g n) R R.contDiff.contDiffAt rfl] at he
   have hx:=he;rw [fit_translate] at hx;simp only [coeff_map] at hx;change MvPolynomial.rename id _=mixRows _ _ at hx;rw [MvPolynomial.rename_id_apply] at hx; unfold rancho;rw [←target]; exact congr_arg (marble r) hx
lemma leadingInk (V : Tile (edgeL G) r)(S:(n:Side)→Pap (wire G n))(j) (h:Light V (fun n=>rancho (S n) j r)) (hp : ∀ᶠ n in atTop,Glare (S n) E)(he:j≤ E) : Lust V:= by
   intro g u; have ht := tendsto_finsetSum (Finset.univ : Finset (chain (hue G) r)) (fun v _=> (h (fun i=>rowD (u i) (v i))).mul_const (∏ i,suit g (v i) (u i).2.2))
   refine tendsto_nhds_unique (h u) (ht.congr' ?_); filter_upwards [hp] with n hn;exact ((congr_fun (luster g (S n) hn j r he) (Lotus.drip n ∘ u)).trans (unshot g _ _)).symm
structure Glyph (o:Loc G 1)(T:Anthem D G)(u E:ℕ):Prop extends IsLinearMap ℝ T where
    summary: Wade o T u
    glows:∀ n p, Glare (Kemp.banner u (T p) n) E
variable {o:Loc G 1}{T:Anthem D G}
lemma from_clef (h:Clef o T u)(E): Glyph o T u E:={ h.toIsLinearMap with
    summary:= h.fare, glows:= fun n p I _ a b k hA hB hC hd hk ht hy j _ => congr_arg (coeff j) (((solo_iff T).mp h.ward n p) I a b k hA hB hC hd hk ht hy) }
lemma lightS (h:Wade o T u)(j n:ℕ)(p):Light (T p j n) (fun m=> rancho (Kemp.banner u (T p) m) j n):= by obtain ⟨η,C,hη,-,he⟩:= h.2.2 j n; simp_rw [badge (T p) (h.1 p) (h.2.1 p) le_rfl]; exact (sieve_kalm _ (he p) hη.le).1
lemma Glyph.color (h:Glyph o T u E)(e r:ℕ)(hx:e≤ E)(p): Lust (T p e r):=leadingInk _ (Kemp.banner u (T p)) e (lightS h.summary e r p) (.of_forall fun n=> h.glows n p) hx
lemma cruises_void {U:Pot G}(h:U e=0)(z:hue G)(x:Cover)(r k):cruisesD z x (e,k) r U=0:= by
   have he (v:City.Pane G (Four ℤ)) l: shapeD z v l (e,k) r U=0:= by
      unfold shapeD; refine Finset.sum_eq_zero fun i _=>?_; rw [plaster]; rw [show ∀ n, U e n=0 from congr_fun h, show shed (0:Tile _ _) v=0 from rfl, show clutch (0:Tile _ _) (_:Tile (edgeL G) _) =0 from ?_,sand_nil,length_void,smul_zero]; funext j; simp [clutch]
   unfold cruisesD; simp_rw [he,zero_add,Finset.sum_const_zero]
lemma Glyph.tapped (h: Glyph o T u E)(hx:e≤ E)(hp:∀ j<e,∀ p,T p j=0)(p): Grail.Torrid (T p e r) σ 0 o:= by
   cases r with
   | zero=> intro r hr; omega
   | succ r=>
       apply Grail.current.mpr
       have he z x:= leadTap z x e r (T p) (Kemp.banner u (T p)) (fun i j _=>lightS h.summary i j p) (.of_forall (fun n=>h.glows n p)) hx
       have ht z x: City.riverP z x (T p e (r+1))=0:= by
          have he':=he z x; rw [Finset.sum_eq_single (e,0),City.cruise_head z _ e (h.summary.2.1 _ _ _)] at he'
          · exact (smul_eq_zero.mp he').resolve_left (by positivity)
          · rintro ⟨j,n⟩ H h'; exact cruises_void (hp j (by have he:= Finset.mem_antidiagonal.mp H; simp at h';simp only at he; omega) p) _ _ r n
          simp
       rw [show tap (T p e (r+1))=0 from funext fun i=> congr_fun (ht (i 0).2.2 (i 0).1) (Fin.tail i)]; apply Knox_zeros
end YM.FormalBulk08.Spigot
