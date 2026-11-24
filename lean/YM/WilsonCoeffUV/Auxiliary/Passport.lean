import YM.WilsonCoeffUV.Auxiliary.Plates
/-!
# Auxiliary tape any sufficiently large odd plate sizes

No β estimates assumed in use. Q.growth etc just used to issue placeholder A witnesses. Can pad arbitrarily long input windows. All tape identifications still refer to their exact L & J & stencils. No claims on real matching (including along this chain). AuxPlates ports
expose stencil- and geometry-conditions for its coefficient bounds.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.AuxPlates
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil Power
open Embroider Precision Exterior Source Source.Drops Labels WardBin Cosmos Bulb Realm Fountain PathCost Supply Ticket Shard Plan Mer Patrol Polestar
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{h k u e n D j s a:ℕ}{H:Hol G} {R:Master H} {p:Sheet G} {Q: Rolls p}{Ω:Protection Q}{Y:Delays Ω}{F':ℕ→ℕ}{Ñ:ChartRatio G}{y:ℕ→ℝ} {A:Levels G}

/-- Extend rolls to use two arbitrary allowed plateau sizes; lower unused entries can be paid through arbitrary sheet, too. This lets neighboring ratio switches have comparable costs ON either candidate. -/
lemma any_two (p:Sheet G)(h:G.Simple) : ∃ f:ℕ,∀ L L':Side, f ≤ L.val → f ≤ L'.val → Odd L.val → Odd L'.val → L.val≤L'.val →∃ Q:Rolls p,Q.L p.first=L ∧ Q.L (p.first+1)=L':=by
    choose C H using fun i=>Rolls.eventually_large p h i; let M:=fun i=>(Finset.range (i+1)).sup C
    have hm:Monotone M:= fun i j hij=>Finset.sup_mono (Finset.range_mono (by omega)); have hh i:C i≤M i:= Finset.le_sup (Finset.mem_range.mpr (by omega))
    let v:= p.first; refine ⟨M (v+1),fun L W g z ho x q=>?_⟩; let f i: Side:=⟨2*M i + 2*W.val+1,by omega⟩; let t:=fun i=>if i≤v then L else if i=v+1 then W else f i
    have H' i:M i ≤ (f i).val:=by dsimp [f]; omega
    have e i:W.val ≤ (f i).val:=by dsimp [f]; omega
    have P : ∀ j,Large p j (t j):=by
        intro j; unfold t; split_ifs with h' h'
        · exact H _ _ ((hh j).trans ((hm (by omega : j≤v+1)).trans g)) ho
        · subst j; exact H _ _ ((hh _).trans z) x
        exact H _ _ ((hh _).trans (H' j)) ⟨M j+W.val, by dsimp [f]; omega⟩
    have T:Monotone fun j=>(t j).val:=by
        intro i j p; have ext_i : (f i).val=2*M i +2*W.val+1:=rfl; have ext_j : (f j).val=2*M j + 2*W.val+1:=rfl; have h:=hm p; dsimp only [t]; split_ifs with a b c d <;> omega
    exact ⟨⟨t,P,T⟩,show t v=L by simp [t],show t (v+1)=W by simp [t]⟩

-- unified card for registered horizons etc. no relation asserted on physical quote.
def Ally (R:Master H)(A:Levels G)(Ñ:ChartRatio G)(y:ℕ →ℝ)(e s kD kF:ℕ): Prop:= ∀ (h D k u d:ℕ)(p:h<D)(v:Rails h k u e), h≤ kD → D≤kF → k+d≤kF → u≤ kF →∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧ W.arch.V.y=y∧ W.arch.V.anchor=s∧ Weston W.arch Credit.leanC∧ (∀ i (v:W.arch.V.anchor≤ i), ∃ p:5≤A.clock.J (i+1),(W.arch.angle i v).lamp.exitS=crestM A i p) ∧ Z.L=W.arch ∧∀ k'≤ k,∀ d'≤ d, Dormitory W.arch.V k' u Credit.leanC ∧ SpringD W.arch.V k' u (k'+d') Credit.leanC
lemma auxAlly (g:G.Simple)(hA:LocalRatio Ñ)(a:BasicBill Y A y s)(f:AwardsM H R F' Q Ñ Y) (h':∀ j≥ s, let v:=A.clock.J (j+1);5≤ v ∧ h+1 ≤ v-2 ∧ max k (e+1) ≤ F' v) : Ally R A Ñ y e s h k:=by
    intro i d m u w p v h k D u; apply qualifiedBright g hA a f p v; intro j z; obtain ⟨x,t,e⟩:= h' j z; omega
variable {K:KernelChoices}
theorem flat_passport (g:G.Simple) (R: Master H)(Ñ:ChartRatio G)(hA:LocalRatio Ñ)(K:KernelChoices)(hk:∀ P:Patch,P.Branches K G) (e h k i:ℕ)(q:h+3≤ i)(v:5≤ i) : ∃ f:ℕ, ∀ L L':Side,f ≤ L.val → f≤ L'.val → Odd L.val → Odd L'.val → L.val ≤ L'.val →∃ C:ℝ,1≤C∧ ∀ n c:ℕ,c≤n→ ∃ A: Levels G, ∃ s:ℕ,A.clock.kernel=K ∧ A.clock.factor i=L ∧ A.clock.factor (i+1)=L' ∧ Walk A i c s n ∧ Ally R A Ñ (extendedY C A.S (s+n)) e s h k:=by
    obtain ⟨t⟩:= cap_st
    let X:=fun _ :ℕ=>max k (e+1); let p:Sheet G:= ⟨K,hk,fun _=>t,i,by omega,monotone_const,monotone_const,monotone_const,horiz H R Ñ X K⟩
    obtain ⟨f,F⟩:= any_two p g; refine ⟨f,fun L L' h p' v1 v2 t=>?_⟩; obtain ⟨W,hP,hQ⟩:= F L L' h p' v1 v2 t
    obtain ⟨Ω,ho⟩:= Protection.exists_margin W (fun _=>1) (fun _=>zero_lt_one); let Y:Delays Ω:= ⟨aperture H R Ñ X W,0,0,0⟩; obtain ⟨o,_⟩:= Bar.exists_above Y 1
    obtain ⟨C,hC,h⟩:= finite_plates g o; refine ⟨C,hC,fun n c p'=>?_⟩; obtain ⟨A,start,B,V,t,a⟩:= h n c p'
    have he:p.first=i:=rfl
    have hR: A.clock.factor i=L:= by rw [t.lengths,←he,hP]
    have hS:A.clock.factor (i+1)=L':=by rw [t.lengths,←he,hQ]
    refine ⟨A,start,a.kernel,hR,hS,V,auxAlly g hA a (reported H R (F':=X) (show _=_ from rfl).le (show _ ≤ Y.betaEntry from le_rfl)) (fun j hj=>?_)⟩; have hz:A.clock.J 0=i:=t.firstZero; have hg:= A.fits.mono (show 0≤j+1 by omega); exact ⟨by omega,by omega,le_rfl⟩

-- Turns full inputs. explicit enrollment no waiting for arbitrary constructor.
lemma Ally.onwards {a h' k':ℕ} {P: Fin (a+1)→SealR G} (v : Rails h k u e)(p:h<D)(x:Ally R A Ñ y e s h' k')(l:h≤h')(L:D≤k')(L':k+2≤ k')(S:u≤ k')
   (t:∀ i,BayV R (P i).h (P i).D (P i).path=P i)(w: capP P≤k)(q: ∀ i, (P i).h≤h'∧ (P i).D ≤k'∧∃ u':ℕ,u'≤k'∧ Rails (P i).h (P i).h u' e): ∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧ W.arch.V.y=y∧ W.arch.V.anchor=s∧ Weston W.arch Credit.leanC∧ W.arch=Z.L∧ Dormitory Z.L.V (capP P) u Credit.leanC ∧ SpringD Z.L.V (capP P) u (capP P+2) Credit.leanC ∧ FramesR H Z.L.V Credit.leanC Credit.leanC P Credit.leanC ∧ HorizonP H Z.L.V Credit.leanC Credit.leanC P:=by
    obtain ⟨W,Z,a,b,c,d,h,s',g,z⟩:= x h D k u 2 p v l L L' S
    obtain ⟨r,V⟩:= z _ w 2 le_rfl; refine ⟨W,Z,a,b,c,d,h,g.symm,?_⟩; rw [g]
    have hp:FramesR H W.arch.V Credit.leanC Credit.leanC P Credit.leanC:=by
       intro i; obtain ⟨j,v,k,e,w⟩:= q i; obtain ⟨Y,Q,p,l,L,L',X,z⟩:= x _ _ _ _ 0 (P i).path w j v (by simpa only [Nat.add_zero] using ((P i).path.le.trans v)) e
       rw [← t i]; exact ⟨⟨⟨Y,p.trans a.symm,l.trans b.symm,L.trans c.symm,L'.trans d.symm⟩,X⟩⟩
    exact ⟨r,V,hp, fun j=>(hp j).map fun v=>v.p⟩
end YM.WilsonCoeffUV.AuxPlates
