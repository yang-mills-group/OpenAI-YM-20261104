import YM.SignedWilsonExpansion.TraceE
import YM.FVA2.Lambda.Pages
namespace YM.SignedWilsonExpansion.TorchE
/-! # Temperature derivative after differentiating in cutoff length.

Exterior term and surviving local **quartic** contact in formula. The actual
high mark equation flows both in momentum and in the coupling variable; we
first pass the derivatives through ∫ from that continuum equation. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake MS.Momentum
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open MS.Osc MS.Osc.Snap MS.Latch MS.Latch.Job MS.Hem MS.Hem.Mell MS.Rock MS.Rock.Path
open FVA2 FVA2.Lambda Area Walk Bubble TreeLine TreeView HighRank HighScale MarkRows MassShift
open scoped Classical Topology ContDiff BigOperators
open Energy (plane leg firstE)
variable {G:Gauge} {a b c d i j u v l:Axis} {A B Cc:G.ColorIndex} {p q r k x:FourP} {n:ℕ}
    {h:ℝ→ℝ} {s t:ℝ}
local notation "Ψ"=>field (P:=FourP) (Landau.parity (A:=Axis) (C:=G.ColorIndex))
local notation "ωβ" => [W i A p,W j B q] -- orientation external different allowed.
lemma smooth_amp : ContDiff ℝ ∞ (amp t):= amp_smooth.comp (f:=fun x:ℝ=>(t,x)) (contDiff_const.prodMk contDiff_id)

section smooth_read
variable {F H:Law G} {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma head_smooth (hp:Polish F)(p:Lane4 G) : Polish ( D p F ):= by
    intro E _ _ w; unfold fieldVal; simp_rw [ at_D ]; let X : Plane.Wire (Branch G Axis) (FourP×E) FourP:= w.map fun v=> (v.1,v.2.comp (ContinuousLinearMap.snd ℝ FourP E))
    have ht : ∀ x:E,p::sail w x=sail ((p.1,ContinuousLinearMap.fst ℝ FourP E)::X) (p.2,x):= by
        intro x; have hx : sail w x=sail X (p.2,x):= by unfold X sail; rw [List.map_map]; rfl
        rw [hx, sail_cons]; rfl
    simp_rw [ ht ]; exact (hp _ _).comp (f:=fun x:E=> (p.2,x)) ( contDiff_const.prodMk contDiff_id )
lemma trc_p (hp:Polish F) (K:TreeLine.Line G) (p:FourP) : Polish ( trc K p F ):= by
   intro E _ _ w; unfold fieldVal; simp_rw [at_trc]; exact ContDiff.sum fun i _=> ContDiff.sum fun j _=> contDiff_const.mul ( ( head_smooth ( head_smooth hp (i,p) ) (j,-p) ) E w )
lemma rootP : Polish (TraceE.root (amp t) (G:=G)):= by
    rw [TraceE.root,← cub_eq,Canvas.quad, show Canvas.line4 G (amp t)=TreeLine.chi G t from ampL.symm]; exact Polish.add BulkTop.qua_p ((BulkTop.cub_p.chi BulkTop.cub_p t).smul _)
lemma sail_eq (x:ℝ) (w:List (Lane4 G)): sail (ray w) x=w.map (fun u=>(u.1,x • u.2)):= by induction w with| nil=>rfl| cons i w ih=>simp [ih]
lemma leg_length (x:ℝ)(p:FourP): leg a b i ( x • p ) = x* leg a b i p:= by unfold leg; rw [mul_sub]; split_ifs <;> simp [smul_eq_mul]

-- EmptyRead: not visible through order 3
def emptyR (f:ℝ→ℂ) : Prop:= ∃ A:ℝ→ℂ, ContDiff ℝ ∞ A ∧ ∀ x:ℝ,f x=(x^4:ℝ) • A x
variable {f f':ℝ→ℂ}
lemma emptyR.read (p:emptyR f)(v:ℕ)(hv:v≤3): reading v f=0:= by
    obtain ⟨A,h,hA⟩:=p; let t (x:ℝ):= (x^4:ℝ) • (1:ℂ);
    have hx: f= fun x:ℝ=>t x*A x:= funext (fun x=> by rw [hA]; simp [t,Complex.real_smul]); rw [hx, Plane.read_mul ( show ContDiff ℝ ∞ t from (by unfold t; fun_prop) ) h ]; refine Finset.sum_eq_zero fun i hi=> ?_; rw [show reading i t= _ from read_pow .., if_neg (by rw [Finset.mem_range] at hi; omega),zero_mul]
lemma emptyR.smooth (H:emptyR f): ContDiff ℝ ∞ f:= by obtain ⟨A,H,he⟩:=H; rw [ funext he ]; fun_prop
lemma emptyR.add (H:emptyR f)(h:emptyR f'): emptyR (fun x=> f x+f' x):= by
    obtain ⟨A,H,he⟩:=H; obtain ⟨Q,h,ha⟩:=h; exact ⟨ A+Q,H.add h,fun x=>by dsimp only; rw [he,ha]; exact (smul_add ..).symm ⟩
lemma emptyR.sum {K:Type}{f:K→ℝ→ℂ}(s:Finset K)(hp:∀ i∈s,emptyR (f i)): emptyR (fun x=>∑ i∈s,f i x):= by
    induction s using Finset.induction with
    | empty=> exact ⟨ 0,contDiff_const, fun x=> (by simp) ⟩
    | insert i s hi ih=> simp_rw [ Finset.sum_insert hi ]; exact emptyR.add ( hp _ (by simp) ) (ih (fun j h=>hp j (Finset.mem_insert_of_mem h)))
lemma emptyR.mul (H:emptyR f)(hf:ContDiff ℝ ∞ f'): emptyR (fun x=> f x*f' x):= by obtain ⟨A,H,he⟩:=H; exact ⟨ A*f',H.mul hf, fun x=>by dsimp only; rw [he]; exact smul_mul_assoc .. ⟩
@[local fun_prop] lemma smooth_cast : ContDiff ℝ ∞ ((↑) :ℝ →ℂ):= Complex.ofRealCLM.contDiff
lemma vacant (H: ContDiff ℝ ∞ h) : emptyR (fun x:ℝ=> ( (strength a b h (x • p) i*leg a b j (x • q):ℝ): ℂ )):= by
    unfold strength Momentum.sq -- shouldn't expand ?
    let A :ℝ→ℂ:=fun x=> ↑(4*p.sq*h ((x • p:FourP).sq) * leg a b i p * leg a b j q)
    change emptyR (fun x:ℝ=> ( (4*(Momentum.sq (x • p))*h ( Momentum.sq (x • p) ) *leg a b i (x • p)*leg a b j (x • q):ℝ): ℂ ))
    refine ⟨ A,(by unfold A; unfold Momentum.sq; fun_prop), fun x=>?_ ⟩; unfold A; simp_rw [scaling, leg_length]; simp only [Complex.real_smul]; push_cast; ring
lemma sPol (P:Polish F)(w:Legs (Lane4 G)) : ContDiff ℝ ∞ (fun x:ℝ=> F (sail (ray w) x)):= P ℝ _
lemma seenS (hp:Polish F): ContDiff ℝ ∞ (fun x:ℝ=>F [W i A (x • p),W j B (x • q)]):= by
    obtain he:= sPol hp ωβ; simpa [sail_eq,W,qnote] using he
lemma skipF (P:Polish F)(hv:ContDiff ℝ ∞ h) : emptyR (fun x:ℝ=> changeF (x • p+x • q) a b h F (sail (ray ωβ) x)):= by
    have he(x:ℝ): sail (ray ωβ) x=[W i A (x • p), W j B (x • q)]:= rfl -- by simp
    simp_rw [he,Walk.chosen,c_empty]; simp_rw [add_zero,picked,at_D, show ∀ x:ℝ, x • p-(x • p+x • q)=x • (-q) from fun x=>by rw [smul_neg]; abel, show ∀ x:ℝ, x • q-(x • p+x • q)=x • (-p) from fun x=>by rw [smul_neg]; abel]
    exact emptyR.add (emptyR.sum _ (fun _ _=> (vacant hv).mul (seenS P))) (emptyR.sum _ (fun _ _=> (vacant hv).mul (seenS P)))
lemma skipH (hp:Polish F)(hv:ContDiff ℝ ∞ h) : emptyR (fun x:ℝ=> Flux.tree parity (lineL G h) F (plane a b G 0) (sail (ray ωβ) x)):= by
    have he(u v:FourP) : Flux.tree parity (lineL G h) F (plane a b G 0) [W i A u,W j B v]=pick (u+v) a b h (W j B v) [W i A u] F+pick (u+v) a b h (W i A u) [W j B v] F:= by
       unfold tree; simp only [ scatter_cons, scatter_nil ]; rw [show attaches parity (lineL G h) F (plane a b G 0)=_ from (show attaches parity (lineL G h) F (plane a b G 0)= R G h F (plane a b G 0) from rfl) ]; rw [ rejected F (_::_::_ ) [] (by simp), rejected F [] (_::_::_ ) (by simp), used (u+v) F _ j B v (by simp [net,W,qnote]), used (u+v) F _ i A u (by simp [net,W,qnote,add_comm]) ]; simp only [ show Ψ (W i A u)=false from rfl, show Ψ (W j B v)=false from rfl,cross_false,mul_zero,add_zero, one_mul,zero_add]; abel
    simp_rw [ show ∀ (x:ℝ), sail (ray ωβ) x=[W i A (x • p), W j B (x • q)] from fun _=> rfl, he, picked, show ∀ x:ℝ, x • p-(x • p+x • q)=x • (-q) from fun x=>by rw [smul_neg]; abel, show ∀ x:ℝ, x • q-(x • p+x • q)=x • (-p) from fun x=>by rw [smul_neg]; abel ]
    exact emptyR.add (emptyR.sum _ (fun _ _=> (vacant hv).mul (seenS hp))) (emptyR.sum _ (fun _ _=> (vacant hv).mul (seenS hp)))

end smooth_read
open MS.Puff MS.Arc MS.Train MS.Wind -- scope check
variable {K:Booked (Press.portDeck G)}
local notation "D0" => spaceD G
variable (M:MS_Data G K)
local notation "U" => Archive 4 M.bulk
local notation "R" => packet M
local notation "V" => Energy.called a b G
local notation "X" => plane a b G 0

-- Wallet justification before opening second derivatives in ∫; reuses bound of actual mark.
lemma bright (u:MarkRows.I (Press.portDeck G)→ℝ) (S:Clock ℝ) : R u 2 S∈ Breeze.Wallet G:= by
    rw [own]; refine Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ ?_;
    have hv:= (markView M (address i) 2|>.host)
    refine Breeze.permits.mpr (fun E _ _ w=>?_); rw [Breeze.spaceArc]; exact Outlook.BigG (hp:=( blade0 (s:=S.2) (y:=S.1) hv ).price ) 0 w -- smell
lemma major_mark (S:Clock ℝ)(w:Legs (Lane4 G)) : Majorant (covMeasure Axis) (fun k (x:ℝ)=> trc (PlanetD G t) k (R V 2 S) (sail (ray w) x)):= by
    let Z:= Job.single Unit; have hp:= bright M V S; have hw:= Latch.topCycle (w:=ray w) ( Latch.Lease.highp (show Latch.Lease false false Z (fun _=> R V 2 S) 1 from hp)) ( Breeze.SheetU t ) (fun i=> Bool.noConfusion i) (fun _=>zero_le_one) (fun _=> zero_le_one)
    exact MS.Rapid.major ( Reserve.cover (S:=Z) (μ:=covMeasure Axis) ( Module.finrank ℝ QP+1) (by unfold QP; omega) ) hw ()
lemma only_force (simple:G.Simple)(S:Clock ℝ) : recu D0 0 1 U (R V) 2 S ωβ=
        cycle (PlanetD G S.2) (covMeasure Axis) (R V 2 S) ωβ +Flux.tree parity (PlanetD G S.2) (U 2 S) X ωβ:= by
    unfold recu; rw [tree_second, Pi.add_apply,Pi.add_apply]; let L:= PlanetD G S.2
    rw [MarkShift.compare_context ( «X» := U 2 S ) ( Y:= U 2 S ) ( «V» :=R V 0 S ) (K:=(D0).meter S.2) (fun _ _ _=> rfl) (fun w h=> MarkRows.starts M V S w h),
        Energy.found ]
    rw [ tree_height _ (Archive 4 M.bulk 1 S) _ _ false (fun t=>Bool.noConfusion t), add_zero]; rfl
    intro i j hv; have e:i+j=2:= by simpa using hv -- check argument order
    by_cases hi:i=2
    swap; · left; intro w ht hw; rw [BulkTop.paid1 M simple S w (by omega) ht]; exact BulkTop.bulk1_r (G:=G) 0 w (by rw [mod_int]; omega)
    right; intro w _ hw; obtain ⟨w,rfl⟩:= List.length_eq_one_iff.mp (show w.length=1 from by omega)
    exact MarkShift.mark_single M V 1 S w simple

lemma cut_keep (simple:G.Simple)(S:Clock ℝ) :
    torch 2 (recu D0 0 1 U (R V) 2 S) ωβ = ∫ k:FourP, reading 2 (fun x:ℝ=> trc (PlanetD G S.2) k (R V 2 S) (sail (ray ωβ) x)) ∂(covMeasure Axis):= by
    let A := fun x:ℝ=>∫ k, trc (PlanetD G S.2) k (R V 2 S) (sail (ray ωβ) x)∂(covMeasure Axis)
    let E := fun x:ℝ=>Flux.tree parity (PlanetD G S.2) (U 2 S) X (sail (ray ωβ) x)
    have he(t:ℝ): recu D0 0 1 U (R V) 2 S (sail (ray ωβ) t)=A t+E t:=only_force (p:=t • p) (q:=t • q) M simple S
    have hp:Polish (U 2 S):= fun E _ _ w=> Outlook.hair (bulkView M 2 (by decide)|>.host) (n:=0) w
    have hM: emptyR E:= by unfold E; rw [dotL]; exact skipH hp (by unfold Shells.hot; fun_prop)
    have hx:= major_mark (a:=a) (b:=b) (t:=S.2) M S ωβ
    rw [torch_at,funext he,Plane.read_add ( f:= A ) hx.contDiff hM.smooth,hM.read 2 (by decide),add_zero]; exact Pages.sponge _ hx 2
lemma trc_integrable (S:Clock ℝ)(w:Legs (Lane4 G)) : Integrable (fun k:FourP=> reading n (fun x:ℝ=> trc (PlanetD G S.2) k (R V 2 S) (sail (ray w) x))) (covMeasure Axis):= by
    simp_rw [reading, iteratedDeriv_eq_iteratedFDeriv]
    let L:= ContinuousMultilinearMap.apply ℝ _ ℂ ( (fun _=>1) : Fin n→ℝ )
    have hu:= L.integrable_comp ( ( major_mark (a:=a) (b:=b) (t:=S.2) M S w ).integ n 0 ); exact hu.smul ((Nat.factorial n:ℝ)⁻¹) -- search

local notation "w" => [W i A p,W j A q]
-- pointwise static local contact comparison
lemma contact_mark (S:Clock ℝ)(r u:FourP) :
      let F:=TraceE.peak a b S.2 G
      let L:=MarkTop.markTopLocal M V (firstE a b G 0)
      trc ( PlanetD G t ) k (R V 2 S) w=trc ( PlanetD G t ) k L [W i A r,W j A u]+trc ( PlanetD G t ) k F w:= by
   intro F L; simp only [at_trc, ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=>?_;
   rw [ MarkTop.evaluation M V (firstE a b G 0) Energy.full S _ rfl ]; rw [ show MarkTop.markTopLocal M V (firstE a b G 0)=L from rfl,mul_add ];
   suffices hv : L ((x,k)::(y,-k)::[W i A r,W j A u])=L ((x,k)::(y,-k)::w) by rw [ hv ]
   let L':=( R V 2 - ( MarkTop.charged V (firstE a b G 0) ∘ Prod.snd ))
   let v:= ((x,k)::(y,-k)::[W i A r,W j A u]); have hl: fieldDim wfield v=fieldDim wfield ((x,k)::(y,-k)::w):= rfl
   have ht:= MarkTop.static_top M V _ Energy.full; have hp:= length_pay v; have hn:v.length=4:= rfl
   rcases eq_or_lt_of_le hp with h|h
   · exact flat_spins_static (f:=L') (0,0) ht v _ (fun i=> Bool.noConfusion i) (fun i=> Bool.noConfusion i) rfl h.symm rfl
   rw [hn] at h; exact (ht.over _ _ v (fun i=>Bool.noConfusion i) rfl h).trans (ht.over (0:ℝ) 0 _ (fun i=>Bool.noConfusion i) (by rfl) (hl ▸ h)).symm -- meta

def rawE (t:ℝ)(k:FourP)(a b:Axis)(G:Gauge)(i j:Axis)(p q:FourP):ℂ:=
    ↑(G.casimir*Shells.hot t k.sq *(TraceE.complete (amp t) a b p q i j k+TraceE.complete (amp t) a b p q i j (-k)))
lemma focus_mark (simple:G.Simple)(S:Clock ℝ) :
    reading 2 (fun x:ℝ=> trc (PlanetD G S.2) k (R V 2 S) (sail (ray w) x))
    = reading 2 (fun x:ℝ=> rawE S.2 k a b G i j (x • p) (x • q)):= by
    let L:=PlanetD G S.2
    let A0:= fun t:ℝ=> rawE S.2 k a b G i j ( t • p ) ( t • q )
    let E0:= fun t:ℝ=> changeF (t • p+t • q) a b (amp S.2) ( trc L k ( TraceE.root (amp S.2) ) ) (sail (ray w) t)
    let v:=trc L k (MarkTop.markTopLocal M V (firstE a b G 0)) w
    let H t:=trc L k (R V 2 S) (sail (ray w) t); have hp : emptyR E0:= skipF (trc_p rootP L k) smooth_amp
    have he(x:ℝ): H x=v+(A0 x+E0 x):= by
       unfold H v E0; rw [show sail (ray w) x=[W i A (x • p), W j A (x • q)] from rfl, contact_mark M S p q ]; unfold L; rw [dotL, TraceE.formula _ simple]; rfl
    have ht:A0 = H-(fun _=> v)-E0:= by funext x; rw [Pi.sub_apply,Pi.sub_apply,he]; abel
    have hm:ContDiff ℝ ∞ A0:= by rw [ht]; exact ((sPol (trc_p (MarkRows.polish M V 2 S) L k) w).sub contDiff_const).sub hp.smooth
    change reading 2 H=reading 2 A0
    rw [ funext he, read_add contDiff_const (hm.add hp.smooth), read_add hm hp.smooth,hp.read _ (by decide),add_zero, show reading 2 (fun _:ℝ=> v)=0 from (by simp [reading,show (2:ℕ)=1+1 from rfl, iteratedDeriv_succ]),zero_add ]

lemma projector (simple:G.Simple)(S:Clock ℝ) :
    torch 2 (recu D0 0 1 U (R V) 2 S) w = ∫ k:FourP, reading 2 (fun t:ℝ=> rawE S.2 k a b G i j (t • p) (t • q)) ∂(covMeasure Axis):= by rw [cut_keep M simple S]; simp_rw [ focus_mark M simple S ]


end
end YM.SignedWilsonExpansion.TorchE
