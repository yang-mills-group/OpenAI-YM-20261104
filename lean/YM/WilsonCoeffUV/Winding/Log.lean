import YM.WilsonCoeffUV.Winding.Pitch
/-!
# Full normalized LOG export at one matched Q step.
No dilation even global marks. Γ from explicit formal step. Exponential
agreement even all roots held simultaneously with true offsets (J or subset,
as always shaped) if 4*joint support < side. See aliases at delivery for
point/all Alias fibers.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Wheel Wheel.Mark Cosmos Mer Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type}{G:Gauge}{D k:ι→ℕ}{i j k' r e a l:ℕ}{s A B C W t q :ℝ}
variable {J Z S:Finset ι}{p:ι→Cover}{x:ι}[DecidableEq ι]

-- reset powers are consumed only in those intervening orders.
structure PackOne (J:Finset ι)(D k:ι→ℕ)(e:ℕ)(I:Arch G) where
    V : ScrollV e I
    w : ι→Cover
    b : ι→ Site I.P.L
    K : family G D
    size : shellK 2 V.W'
    form (i:ℕ): Pure (V.W' i)
    undo : K ∅=0
    awake : Eu k K
    A : ℝ
    lih : 0≤ A
    shore (S:Finset ι)(x:S⊆ J)(j:ℕ)(p:j≤ e)(r:ℕ) : MarkU (chartIn I.P w b) S ((K S).1 (V.n*I.P.L) j r) ((K S).2 j r) I.s (A^S.card)

namespace PackOne
variable {I:Arch G}(p:PackOne Z D k e I)
abbrev M:= p.V.landing
abbrev N:= p.V.rampU
abbrev surfU (J:Finset ι)(i j:ℕ):= bend (I.roll p.V.n) (inHeat p.V.wheel p.V.shadow p.V.H (p.V.T p.V.n) I.R p.V.W' p.K J i j)
abbrev surfC:= Humour I.P I.K I.R p.V.γ p.V.M p.V.Z p.K
lemma first (J:Finset ι)(i:ℕ): p.surfU J 0 i=fade (upper 1 (allotM (I.peg p.V.n) (Equiv.refl _) p.V.cone)) (bend (I.peg p.V.n) ((p.K J).1 (p.V.n*I.P.L) i)):=by
   unfold surfU; rw [coldE p.V.wheel p.V.shadow p.V.H _ I.R p.V.W' p.K p.size I.pay p.awake p.undo J, srCold,bend_fade (I.peg p.V.n) (I.roll p.V.n), show allotM (I.peg p.V.n) (I.roll p.V.n) _=upper 1 _ from cam_chart _ _]
lemma more (J:Finset ι)(i j :ℕ):
    p.surfU J (i+1) j=((i+1:ℕ):ℝ)⁻¹ • (ripple p.N (p.surfU J i j)+ravel p.N p.V.vault (p.surfU J) i j+ravel p.N.transpose p.V.vault (p.surfU J) i j+∑ X∈J.powerset, if v:X⊆ J then sewsV p.N v (p.surfU X) (p.surfU (J\X)) i j else 0):=by
    let G':= p.V; let L:=I.P; let n:=G'.n; let g:= ratioN L.L n; let T:=I.roll n; let A:= fillSlots (Woods G n) (covariance G G'.wheel G'.shadow G'.H); let F:=inHeat G'.wheel G'.shadow G'.H (G'.T n) I.R G'.W' p.K
    have hv:=outerS G'.wheel G'.shadow G'.H (G'.T n) I.R G'.W' p.K p.size I.pay p.awake p.form I.trees i j J
    dsimp only at hv
    have he : p.N= allotM T T A:= (lamp_chart g (covariance G G'.wheel G'.shadow G'.H)).symm
    rw [he]; change bend T (F J (i+1) j)=_; dsimp only [F]; rw [hv,bend_smul (W:=Pen D J) T,bend_add,bend_add,bend_add,bend_ripple,bend_ravel,bend_ravel,bend_sum]; apply congr_arg (((i+1:ℕ):ℝ)⁻¹ • ·); apply congr_arg₂ (·+·) rfl; apply Finset.sum_congr rfl; intro u h; have ht:= Finset.mem_powerset.mp h; rw [dif_pos ht,dif_pos ht]; exact bendSean ..
lemma zen (j i r): p.surfU ∅ j i r=0:=by unfold surfU inHeat; rw [turnTLog,dif_pos rfl]; rfl
lemma zen' (i j:ℕ): p.surfC ∅ i j=0:=by
    let A:=p.M
    induction i using Nat.strong_induction_on generalizing j with
    | h i ih => cases i with
      | zero=> unfold surfC Humour; rw [Temple]; unfold slidesJ; rw [p.undo]; funext r x; unfold Bank.prism; rw [climb_cut]; simp [tiles,bend,turnTen]
      | succ i=>
          have hx u: Soil.paintC u p.V.coverVault (p.surfC ∅) i j=0:=by
              unfold Soil.paintC; refine Finset.sum_eq_zero fun a ha=>?_ ; have h:= Finset.mem_antidiagonal.mp ha; apply Finset.sum_eq_zero; intro b _; rw [ih a.2 (by omega)]; funext r; apply Finset.sum_eq_zero; rintro ⟨t,q⟩ hp; have hs:t+q=r:=Finset.mem_antidiagonal.mp hp; subst r; funext x; unfold ruins swivel; simp [Pi.smul_apply,rill_spell]
          have hy: SubC A p.surfC i j ∅=0:=by
              simp only [SubC,Finset.powerset_empty,Finset.sum_singleton,Finset.Subset.refl,↓reduceDIte]; unfold Sewing; refine Finset.sum_eq_zero fun a ha=>?_ ; have h:=Finset.mem_antidiagonal.mp ha; apply Finset.sum_eq_zero; intro b _; rw [ih a.1 (by omega)]; funext r; apply Finset.sum_eq_zero; rintro ⟨u,q⟩ hp; have hs:u+q=r:=Finset.mem_antidiagonal.mp hp; subst r; funext x; unfold ruins swivel; simp [Pi.smul_apply,lakeV]
          have hR : rime A (0:Gen (Pen D ∅) (Cloth I.dial))=0:=by funext r x; unfold rime ruins; simp [rain_spell]
          unfold surfC Humour; rw [warmUp]; change _ • Sat A p.V.coverVault p.surfC i j ∅=_; rw [Sat,hx,hx,hy,ih i i.lt_succ_self,hR]; simp
lemma highest (J:Finset ι)(i j): p.surfC J (i+1) j=((i+1:ℕ):ℝ)⁻¹ • Sat p.V.landing p.V.coverVault p.surfC i j J:= warmUp ..
end PackOne

variable {F:Arch G →Type}
-- orientation and uplift via cob lifts
abbrev primal (G:Gauge)(Z:Finset ι)(D k:ι→ℕ)(e:ℕ)(V : Type)(i:ℕ)(F:Arch G→Type):=(I:Arch G)→(p:PackOne Z D k e I)→Ten V (Co p.V.n (F I)) i
abbrev secondary (G:Gauge)(Z:Finset ι)(D k:ι→ℕ)(e:ℕ)(V:Type)(i:ℕ)(F:Arch G→Type):=(I:Arch G)→PackOne Z D k e I→Ten V (Cloth (F I)) i

def Bursted (P:primal G Z D k e V i F)(Q:secondary G Z D k e V i F) [NormedAddCommGroup V](J:Finset ι):Prop :=∃ d:ℕ, ∀ I, ∃ s C:ℝ, 0<s∧ 0≤ C∧∀ p,MarkU p.w J (P I p) (Q I p) s (C*p.V.coin^d*p.A^J.card)
variable {P Q:primal G Z D k e V i F}{K T:secondary G Z D k e V i F} [NormedAddCommGroup V]
omit [DecidableEq ι] in
lemma Bursted.plus (h:Bursted P K J)(v: Bursted Q T J):Bursted (fun i p=>P i p+Q i p) (fun i p=>K i p+T i p) J:=by
   obtain ⟨d,H⟩:=h; obtain ⟨c,V⟩:=v; refine ⟨max c d,fun I=>?_⟩; obtain ⟨s,A,b,e,g⟩:=H I; obtain ⟨t,B,f,w,x⟩:=V I; refine ⟨min s t,A+B,lt_min b f,add_nonneg e w,fun p=>?_⟩; rw [add_mul,add_mul]; have hp:= p.V.paid; have hx:=pow_nonneg p.lih J.card; exact ((g p).mono (min_le_left ..) |>.more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (le_max_right c d)) e) hx)).add (((x p).mono (min_le_right ..)).more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (le_max_left c d)) w) hx))
omit [DecidableEq ι] in
lemma Bursted.zero: Bursted (F:=F) (fun I (_:PackOne Z D k e I)=> (0:Ten V _ i)) 0 J:=⟨0,fun I=>⟨1,0,one_pos,le_rfl,fun p=> MarkU.zero.more (by simp)⟩⟩
omit [DecidableEq ι] in
lemma Bursted.μ [NormedSpace ℝ V](h:Bursted P K J)(a:ℝ): Bursted (fun i p=>a•P i p) (fun i p=>a•K i p) J:=by
   obtain ⟨d,H⟩:=h; refine ⟨d,fun I=>?_⟩; obtain ⟨s,a',b,e,g⟩:=H I; refine ⟨s,‖a‖*a',b,mul_nonneg (norm_nonneg _) e,fun p=> ?_⟩; apply ((g p).μ a).more; exact le_of_eq (by ring)
omit [DecidableEq ι] in
lemma Bursted.sum {P:X→primal G Z D k e V i F}{Q:X→secondary G Z D k e V i F}(S:Finset X)(h:∀ i∈S,Bursted (P i) (Q i) J):Bursted (fun I p=>∑ i∈S,P i I p) (fun I p=>∑ i∈S,Q i I p) J:=by
    classical
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact Bursted.zero
    | @insert i S hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))

lemma Bursted.hatch (G:Gauge)(i j e:ℕ)(v:i≤ e)(u:J⊆Z)(h:J.Nonempty): Bursted (F:=Arch.dial) (fun (I:Arch G)(p:PackOne Z D k e I)=>p.surfU J 0 i j) (fun _ p=>p.surfC J 0 i j) J:=by
   refine ⟨0,fun I=>?_⟩; let t:= I.s/8; have ht:0<t:=div_pos I.h (by positivity); have hx:t≤ I.s:=by unfold t; linarith [I.h]
   let K:= priceM I.feather j t; have he:0 ≤ K:=priceMP _ _ ht; have hg:= zero_le_one.trans I.book; let u':=(j+1:ℕ)*I.mass^j; have hp:0≤u':=by unfold u'; positivity;
   refine ⟨t/32,K*u'*2*Real.exp (16*I.s),div_pos ht (by positivity),by positivity,fun p=>?_⟩; let R := p.V; let M:= allotM (I.peg p.V.n) (Equiv.refl _) p.V.cone; have hh: Rail (upper 1 M) (upper 1 p.V.M) t I.mass:= by exact (Rail.unit.more I.book).upperL (p.V.lights.mono hx)
   let F:=turnTen (panel I.P.L (Hooks G)).symm ((p.K J).2 i j); have hw:= MarkC.camp (MarkC.trawl ((p.shore J u i v j).pitchIn p.b I.h) hh ht.le) h ht
   dsimp only; rw [p.first]; unfold PackOne.surfC Humour; rw [Temple,slidesJ]; unfold Bank.prism; rw [show Bank.reflectCut _ (tiles I.P.L _ _)=ruins (gloss (upper 1 R.M) F) from funext fun x=> climb_cut _ _]; apply hw.more; rw [pow_zero]; unfold u' K; exact le_of_eq (by ring)

variable {P: (I:Arch G)→(p:PackOne Z D k e I)→ Gen V (Co p.V.n I.dial)}{Q: (I:Arch G) →PackOne Z D k e I → Gen V (Cloth I.dial)}[NormedSpace ℝ V][CompleteSpace V]
omit [DecidableEq ι] in
lemma Bursted.soak (h:Bursted (F:=Arch.dial) (fun i p=>P i p (r+2)) (fun i p=>Q i p (r+2)) J)(v:J.Nonempty): Bursted (F:=Arch.dial) (fun i p=> ripple p.N (P i p) r) (fun i p=> rime p.M (Q i p) r) J:=by
   obtain ⟨d,H⟩:=h; refine ⟨d,fun I=>?_⟩; obtain ⟨s,A,b,g,h⟩:=H I; let t:=min s I.s; have he:0<t:= lt_min b I.h; let u:=priceM I.dial 2 t; have hu: 0≤ u:=priceMP _ _ he; have hh:=zero_le_one.trans I.book; refine ⟨t/32,u*ore r (r+1)*2*I.mass*A,div_pos he (by norm_num),by unfold ore; positivity,fun p=>?_⟩; dsimp only; rw [← Bank.rain_reads]; apply MarkU.more ((MarkC.wet (Q:=P I p) (F:=Q I p) (p.V.rateRamp.mono (min_le_right ..)) ((h p).mono (min_le_left ..)) he.le).camp v he); exact le_of_eq (by unfold u; ring)
variable {M:(I:Arch G)→ (p:PackOne Z D k e I) → ropes (Site p.V.n) I.dial I.dial}{T:(I:Arch G)→PackOne Z D k e I→ ropes Cover I.dial I.dial}
omit [DecidableEq ι] in
lemma Bursted.crunch (h:Bursted (F:=Arch.dial) (fun i p=>P i p (r+1)) (fun i p=> Q i p (r+1)) J)(u:i≤e)(p:∀ I t,Rail (M I t) (T I t) I.s I.mass)(v:J.Nonempty)(f:l+r=a): Bursted (F:=Arch.dial) (fun I p=> wear (swivel (rill (M I p) (p.V.vault j i) (P I p) a l r))) (fun I p=> ruins (swivel (rill (T I p) (p.V.coverVault j i) (Q I p) a l r))) J:=by
    subst a; obtain ⟨d,H⟩:= h; obtain ⟨c,L⟩:= Layered.snowLight G i j e (l+1) u; refine ⟨c+d,fun I=>?_⟩; obtain ⟨s,A,b,w,H⟩:= H I; obtain ⟨t,B,f,g,L⟩:= L I; let z:= min I.s (min s t); have hx:0<z:= lt_min I.h (lt_min b f); let u:=priceM I.dial 2 z; have hu:0≤ u:=priceMP _ _ hx; have hv:= zero_le_one.trans I.book; have hp: z≤ min s t:= min_le_right ..; refine ⟨z/32,u*(ore l r*3*I.mass*B)*A,div_pos hx (by norm_num),by unfold ore; positivity,fun q=>?_⟩; apply ((MarkC.rillL (Z:=q.V.vault j i) (Y:=q.V.coverVault j i) (F:=Q I q) (Q:=P I q) ((p I q).mono (min_le_left ..)) ((H q).mono (hp.trans (min_le_left ..))) ((L q.V).mono (hp.trans (min_le_right ..))) hx.le).swings.camp v hx).more
    rw [pow_add]; exact le_of_eq (by unfold u; ring)
lemma Bursted.stream (h:∀ a:ℕ,a≤j→∀ b ≤ i,∀ r,Bursted (F:=Arch.dial) (fun (I:Arch G)(p:PackOne Z D k e I)=>p.surfU J a b r) (fun _ p=> p.surfC J a b r) J)(u:i≤e)(v:J.Nonempty)(g:∀ I t,Rail (M I t) (T I t) I.s I.mass): Bursted (F:=Arch.dial) (fun I p=> ravel (M I p) p.V.vault (p.surfU J) j i r) (fun I p=> Soil.paintC (T I p) p.V.coverVault (p.surfC J) j i r) J:=by
    unfold ravel Soil.paintC rondel
    simp_rw [Finset.sum_apply, ← Bank.rill_reads]; apply Bursted.sum; intro a x; have hp:= Finset.mem_antidiagonal.mp x; apply Bursted.sum; intro b y; have hx:= Finset.mem_antidiagonal.mp y; apply Bursted.sum; intro z v'; exact (h a.2 (by omega) b.2 (by omega) (z.2+1)).crunch (P:=fun _ p=> p.surfU J a.2 b.2) (Q:=fun _ p=>p.surfC J a.2 b.2) (by omega) g v (Finset.mem_antidiagonal.mp v')
end YM.WilsonCoeffUV.Winding
