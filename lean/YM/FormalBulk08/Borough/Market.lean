import YM.FormalBulk08.Borough.Mint
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Borough
open Lattice Laurent Bloch Precision Stationary RG Wilson Filter Function
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
open Next.Free Reef Flat Dove Dove.Lab North Elm Spigot Aster Source Drops Labels
open RG.Supply Push.PriceCompiler
variable {G:Gauge}{K:KernelChoices}{W:Borough.Window G K}
lemma lodge_owned (P:Patch): Finite (Lodge P):= by
   let _ : Finite Step:= Finite.of_injective (fun x:Step=>(x.dir,x.neg)) (fun a b h=> by cases a; cases b; congr <;> simp at * <;> tauto)
   exact Finite.of_injective Lodge.aim (fun u v h=> by cases u; cases v; congr)
lemma patch_owned {L:Side}{j:ℕ}: Finite {p : Patch // p.L=L ∧ p.J=j} := Finite.of_injective (fun _=> PUnit.unit) (fun x y _=> by
    obtain ⟨⟨u,a,b,c,d⟩,he⟩:=x; obtain ⟨⟨v,w,t,n,m⟩,h'⟩:=y; obtain ⟨e,hf⟩:=he; obtain ⟨p,q⟩:=h'; simp only at e hf p q; subst u a v w; rfl)
variable (Q:Herald)(L:Side)(j t E:ℕ)(K)(F:∀ d,Frame G d)(H:Hol G)(ρ:ChartRatio G)
variable (W:Borough.Window G K)
structure Counter (B:ℝ):Prop where
    size : (L.val:ℝ)≤B
    header : ∀ t≤ j,|(W.width t)⁻¹|+|Avenue.mediumP G K t| ≤ B
    coarse : ∀ t≤j,∀ E≤ j,|cost0 G K (W.width t) t E|+|Broc.shadePrice G E (W.width t)|+|(Broc.bladeC G E (W.width t))⁻¹| ≤ B
    past : ∀ t ≤j,∀ E≤j,∀ (P:Patch)(V:Lodge P),P.L=L→P.J=j→|labelC K (W.width j) (W.width t) (cost0 G K (W.width t) t E) ρ t E P V| ≤ B
    light : ∀ t≤j,∀ d≤ j,∀ E≤ j,∀ D≤ j,∀ R≤j,∀ (o:Loc G 1)(P:Patch)(V:Lodge P),P.L=L→P.J=j→ |Elm.tune (F d) H K o D E R j t (W.width j) (W.width t) P V|≤ B
    render : ∀ t≤j,∀ E≤j,∀ D≤j,∀ l≤j,∀ u≤ j,∀ (o:Loc G 1),|roadC o l u E D Q (W.width t)| + |(inkGate o l u E D Q (W.width t))⁻¹| ≤B
lemma counter_paid : ∃ B:ℝ,0≤ B ∧ Counter K Q L j F H ρ W B:= by
   let I:= Fin (j+1); let v (x:ℕ)(h:x≤ j):I:=⟨x,by omega⟩; let J:= {P:Patch // P.L=L∧ P.J=j}; let P:= (i:J) × Lodge i.val; let _ : Finite J:=patch_owned; let _ (p:Patch): Finite (Lodge p):= lodge_owned p
   obtain ⟨B,b,S⟩:= bddBill (fun i:I=>|(W.width i.val)⁻¹|+|Avenue.mediumP G K i.val|)
   obtain ⟨C,c,T⟩:= bddBill (fun h:I×I=> |cost0 G K (W.width h.1.val) h.1.val h.2.val|+|Broc.shadePrice G h.2.val (W.width h.1.val)|+|(Broc.bladeC G h.2.val (W.width h.1.val))⁻¹|)
   obtain ⟨D,d,N⟩:= bddBill (fun h:I×I×P=> labelC K (W.width j) (W.width h.1.val) (cost0 G K (W.width h.1.val) h.1.val h.2.1.val) ρ h.1.val h.2.1.val h.2.2.1.val h.2.2.2)
   obtain ⟨E,e,G'⟩:= bddBill (fun p:I × I × I × I × I × Loc G 1 × P=>Elm.tune (F p.1.val) H K p.2.2.2.2.2.1 p.2.1.val p.2.2.1.val p.2.2.2.1.val j p.2.2.2.2.1.val (W.width j) (W.width p.2.2.2.2.1.val) p.2.2.2.2.2.2.1.val p.2.2.2.2.2.2.2)
   obtain ⟨M,m,X⟩:= bddBill (fun p:I × I × I × I × I × Loc G 1=> let σ:= W.width p.1.val; |roadC p.2.2.2.2.2 p.2.1.val p.2.2.1.val p.2.2.2.1.val p.2.2.2.2.1.val Q σ|+|(inkGate p.2.2.2.2.2 p.2.1.val p.2.2.1.val p.2.2.2.1.val p.2.2.2.2.1.val Q σ)⁻¹|)
   refine ⟨L.val+B+C+D+E+M,by positivity, ⟨by linarith,fun i h=>(le_abs_self _).trans ((S (v i h)).trans ?_),fun t ht i hi=> (le_abs_self _).trans ((T (v t ht,v i hi)).trans ?_),?_,?_,?_⟩⟩
   · linarith only [L.property,c,d,e,m,Nat.cast_nonneg (α:=ℝ) L.val]
   · linarith only [L.property,b,d,e,m,Nat.cast_nonneg (α:=ℝ) L.val]
   · intro t ht r hr X Z hz hu; exact (N (v t ht,v r hr,⟨⟨X,hz,hu⟩,Z⟩)).trans (by linarith only [b,c,e,m,Nat.cast_nonneg (α:=ℝ) L.val])
   · intro t ht n hn i hi a ha A hA o X Z hz hu; exact (G' (v n hn,v a ha,v i hi,v A hA,v t ht,o,⟨⟨X,hz,hu⟩,Z⟩)).trans (by linarith only [b,c,d,m,Nat.cast_nonneg (α:=ℝ) L.val])
   intro t ht n hn i hi a ha A hA o; exact (le_abs_self _).trans ((X (v t ht,v a ha,v A hA,v n hn,v i hi,o)).trans (by linarith only [b,c,d,e,Nat.cast_nonneg (α:=ℝ) L.val]))
variable {Y:Sheet G}{P:Rolls Y}{T:Protection P} (V:Delays T)
def ageZ (x:ℝ):ℝ:= 1+ Real.log (Real.log x)
lemma progZ {x:ℝ}(h:Real.exp 1≤x): 1≤ageZ x:= by unfold ageZ; exact le_add_of_nonneg_right (Real.log_nonneg ((Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le h)).mpr h))
lemma age_fly : Tendsto ageZ atTop atTop:= tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
structure Prices :Prop where
    allpay:∀ j x, V.betaEntry j≤x → Real.exp 1 ≤ x ∧ ∃ B:ℝ,0≤ B ∧ B ≤ ageZ x ∧ Counter K Q (P.L j) j F H ρ W B
lemma counter_day : ∃ U:Delays T,DelayLe V U ∧ OrderedDelays U ∧∀ V':Delays T,DelayLe U V'→ Prices K Q F H ρ W V':= by
   obtain ⟨X,h,H,R⟩:=delay_extra V (fun j x=> Real.exp 1 ≤ x ∧ ∃ B:ℝ,0 ≤B∧B≤ageZ x∧Counter K Q (P.L j) j F H ρ W B) (fun _ _ _=>True) (fun j=>by
      obtain ⟨B,b,S⟩:= counter_paid K Q (P.L j) j F H ρ W; filter_upwards [eventually_ge_atTop (Real.exp 1),age_fly.eventually (eventually_ge_atTop B)] with i hp hi; exact ⟨hp,B,b,hi,S⟩) (fun _ _=>Filter.Eventually.of_forall fun _=> trivial)
   exact ⟨X,h,H,fun V he=> ⟨(R _ he).1⟩⟩
end YM.FormalBulk08.Borough
