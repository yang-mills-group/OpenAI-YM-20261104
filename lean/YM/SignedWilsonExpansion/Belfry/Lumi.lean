import YM.SignedWilsonExpansion.Belfry.Bridge
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.SignedWilsonExpansion.Belfry
open Function Set Filter Asymptotics PowerSeries Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Menus MS.Book MS.Book.Program MS.Book.Convolve MS.Puff MS.Puff.Actors
open XSpace XSpace.Structure1 XSpace.Normalize FVA2 FVA2.Scale FVA2.Reg FVA2.Dframe
open WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK MarqueQ.Crops MarqueQ.Crops.Taught
open Dancer Commission Belle Belle.Path Belle.Buffet Future
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{ι σ κ κ':Type}{n q m d:ℕ}{L:Filter ι}{θ ε g:ι→ℝ}
namespace ScaleFits
open Belle.Lesson GroupS FVA2.Scale.Level FVA2.Scale.Facets
-- Uniform price before/after scaling and substitution.Wire. finite quotation powers.
section Lamp
variable {A U:Set (Points n)}{F F' : ι→ Points n→Point G d n}
lemma serving (hf:∀ v:Tags G d n,Serves L (fun i x=>F i x v) (fun i x=> F' i x v) U θ) (a:ι→Tags G d n)(b:∀ j, S' (L:=L) (fun i=> a i j)): Serves L (fun i x=> F i x (a i)) (fun i x=> F' i x (a i)) U θ:= by
     let E:= diners L U; let H(i:ι×Points n): Point G d n:= F i.1 i.2-F' i.1 i.2; exact banquet.mpr ( SeatsW.matDiscount (Q:=H) (v:=a ∘ Prod.fst) (fun v=>banquet.mp (hf v)) (fun i t=>(b i t).comp_tendsto plot_le) )
abbrev vis (U:Way G d)(θ:ℝ)(b:ℕ)(x:Points n): Point G d n:= ∑ i∈Finset.range (b+1),(θ:ℂ)^i • Jury.fxt U x i
lemma vision (U:Way G d)(θ:ℝ)(x:Points n)(p:Tags G d n): vis U θ q x p= mote U q x θ p:=by unfold vis; rw [_root_.sum_apply]; rfl
lemma vision_two (U:Way G d)(θ:ℝ)(x:Points n)(p:Tags G d n): mote U q x θ p= invoke (Jury.fxt U x) q θ p:=by
     rw [Path.mote,Taught.invoke,timed]; apply Finset.sum_congr rfl; intro i _; rw [Tape.archive,coeff_mk,mul_comm]
lemma uniformize (X:ι→View G d)(P:Way G d)(hp:∀ f:Tags G d n, Serves L (fun i x=> X i n x f) (fun i x=> mote P q x ( θ i ) f ) U ε) (a:ι→ Tags G d n)(v:∀ j,S' (L:=L) (fun i=> a i j)) : Serves L (fun i x=> X i n x (a i)) (fun i x=> mote P q x ( θ i ) (a i) ) U ε:=by
     refine Serves.fix (serving (F':=fun i=> vis P (θ i) q (n:=n)) (?_) a v) (Eventually.of_forall fun i _ _=> rfl) (Eventually.of_forall fun i y h=> vision ..); intro f; simp_rw [vision]; exact hp f
abbrev ellipse (t:ℝ)(x:Points n): Points n:= Real.exp (-t) • x
lemma vis_conf (t:ℝ)(x:Points n): ellipse t x∈ conf n ↔ x∈ conf n :=by
     refine ⟨fun u=>?_ ,Extent.placed t x ⟩; have hp:= Extent.placed (-t) ( ellipse t x ) u; rwa [ ellipse, ←mul_smul, ←Real.exp_add, neg_neg,add_neg_cancel, Real.exp_zero, one_smul] at hp
lemma fxtL (X:Way G d)(t:ℝ)(x:Points n)(p:Tags G d n) : Jury.fxt ( scaling t X ) x q p= Jury.fxt X (ellipse t x) q (Dial d t ∘ p):=by
     by_cases hx:x∈conf n; · rw [show Jury.fxt _ x=_ from Jury.exactC ( scaling t X ) ⟨x,hx⟩,show Jury.fxt X (ellipse t x)=_ from Jury.exactC _ (⟨_,(vis_conf t x).mpr hx⟩:Stage n)]; rfl
     rw [Jury.fxt,dif_neg hx,Jury.fxt,dif_neg (mt (vis_conf _ _).mp hx)]; rfl
lemma poseM (X:Way G d)(t:ℝ)(x:Points n)(p:Tags G d n)(v:ℝ)(b:ℕ): mote ( scaling t X ) b x v p=mote X b (ellipse t x) v ( Dial d t ∘ p):=by unfold Path.mote; simp_rw [fxtL]
lemma chartR (U:Set (Points n))(a b:ℝ)(p:Roi U) : Roi ( (fun x:ℝ×Points n=> ellipse x.1 x.2) '' (Set.Icc a b ×ˢ U)):=by
     refine ⟨ (isCompact_Icc.prod p.1).image (by unfold ellipse; fun_prop),?_⟩; rintro _ ⟨⟨v,y⟩,⟨hv,hy⟩,rfl⟩; exact (vis_conf _ _).mpr ( p.2 hy )
lemma charter (U:Set (Points n))(p:Roi U)(h:FO L g): ∃ V:Set (Points n),Roi V ∧ ∀ᶠ i in L,∀ x∈U,ellipse ( g i ) x∈V:=by
     obtain ⟨C,a⟩:= isBigO_iff.mp h; refine ⟨_,chartR U (-C) C p,?_⟩; filter_upwards [a] with i h x hx; exact ⟨(g i,x), abs_le.mp (by simpa using h) |> fun v=> ⟨v,hx⟩,rfl⟩
lemma poseD (p:∀ᶠ i in L,∀ x∈U,ellipse (g i) x∈A) : Tendsto (fun i:ι×Points n=>(i.1,ellipse ( g i.1 ) i.2)) (diners L U) (diners L A):=by
     refine Tendsto.prodMk plot_le (tendsto_principal.mpr (?_)); exact diners_clause.mpr p
lemma calendar (u:Roi U)(p:FO L g) {X:Way G d}(v:∀ (V:Set (Points n)),Roi V→ ∀ i (t:Tags G d n),FO (diners L V) (fun j=> Jury.fxt X j.2 i t))(t:Tags G d n)(b:ℕ): FO (diners L U) (fun i=> Jury.fxt ( scaling (g i.1) X ) i.2 b t):=by
    obtain ⟨Y,q,h⟩:= charter U u p; have hp(k:Tags G d n):(fun i:ι×Points n=> Jury.fxt X (ellipse (g i.1) i.2) b k)=O[diners L U](1:ι×Points n→ℝ):= (v Y q b k).comp_tendsto (poseD h)
    have he(j:Fin n):S' (L:=L) (fun i=> (Dial d ( g i )) ( t j )):= SeatsW.translates ( boundD p d ) (LinearMap.applyₗ ( t j )); simp_rw [fxtL]; exact SeatsW.matIncome hp (fun i t=> (he i t).comp_tendsto plot_le)
variable (h:Tendsto θ L (𝓝 0)) {K:Normalize.Store G}(W:Initialize G)(V:Rose.Pick K) (s:G.Simple)
variable {T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S:Prescription (Press.portDeck G)}(Q:Speed.Quoted W V T S)
local notation "X"=> Measure.start W V d
include Q s
-- student reference: B^p->ψ.T^p.Words Uniform in separated parameters.
lemma owedW (h0:Roi U)(b:ℕ)(v:Tags G d n) : FO (diners L U) (fun i=> Jury.fxt X i.2 b v):= Path.cost W V Q s h0 b v
include h
lemma steps (ν:ℝ)(u:Roi U)(p:FO L g)(b:ℕ)(x:Tags G d n) : Serves L (fun i t=> mote X b (ellipse (g i) t) (θ i) ( ( (Dial d ( g i ))*(young b (θ i) (gaugeB V T ν ( g i ) d)) : FieldEnd G d) ∘ x)) (fun i t=> mote X b t (Tick ( GroupS.ψ V T ν ( g i )) (θ i) b) x) U ( θ^b ):=by
     let E:= diners L U; let B:=fun (i:ι×Points n)=> gaugeB V T ν ( g i.1 ) d; let q:= fun (i:ι×Points n)=> GroupS.ψ V T ν ( g i.1 ); let hθ:=θ ∘ (Prod.fst:ι×Points n→ι); let D:=fun (i:ι×Points n)=>Jury.fxt X i.2
     let A(i:ι×Points n):=Jury.fxt ( scaling ( g i.1 ) X ) i.2; let v i:= Tick ( q i ) ( hθ i ) b; have hx(i:ι×Points n):Path.mote X b ( ellipse (g i.1) i.2 ) (θ i.1) ((((Dial d ( g i.1 ))*(young b (θ i.1) (B i)):FieldEnd G d) ∘ x))= invoke (A i) b (θ i.1) ( young b (θ i.1) (B i) ∘ x ):= (poseM (d:=d) X (g i.1) i.2 ((young _ _ _) ∘ x) (θ i.1) b).symm.trans (vision_two ..); have hz: Budget E B:=(checked W V Q s ν p d).comp Prod.fst plot_le; -- check arg order
     let hp'(i):= permit W V Q ν (g i); let T':=h.comp (plot_le (U:=U)); have hzq: Audit E hθ b q (castℂ v):=by
        rw [show castℂ v=(fun i=> calcT (castℂ hθ i) b (q i)) from funext (fun i=> pure_tick (hp' i.1) ..)]; exact amount T' (( eaten W V Q ν p ).comp Prod.fst plot_le )
     obtain ⟨f,y,k⟩:= Q.toContract.toMission.born; have hA(i:ι×Points n): Tape.horizon ( B i ) ( A i )= substitute ( q i ) ( D i ):=by obtain hv:= congr_arg (fun U:Way G d=> Jury.fxt U i.2 ) ( GroupS.actionX ν W V T S s f y k (g i.1) d ); rw [ Jury.fxt_m, Jury.fxt_c] at hv; exact hv; -- type defeq
     have hL:= paidYear (Q:=A) T' (q:=b) x hz ( fun k y=> calendar u p (fun _ h'=> owedW W V s Q h') y k ); have hE:= heeded (Q:=D) T' hzq (fun i=>(hp' i.1).start) (fun _ _=> owedW W V s Q u _ _) x
     apply banquet.mpr; obtain h0:=soldSc T' hL; simp_rw[hA] at h0; refine ( (h0.sub (soldSc T' hE)).congr_left (?_)); intro i; change _- ( invoke (D i) b _ x-_)=mote X b _ _ _ - mote X b _ _ _; rw [hx,vision_two X]; abel -- okay
-- inspect
end Lamp
end ScaleFits
end YM.SignedWilsonExpansion.Belfry
