import YM.SignedWilsonExpansion.F9.Diagonal
import YM.WilsonCoeffUV.Root.UV.RawSemi
/-!
# A complete offshell probe in Mer Ela, and its powers

Do not require any actual qlocal approximation on these additional inputs.
Top linear section gives every needed value. Use `row` only at indicated
rank, so it coincides with its own-coefficient projection, even at positive
order after shifting. Always affix from the actual clock at insertion, then
**reexpress** the scalar at each step.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h p k m N u e i j l r:ℕ}{F:Labels.Frame G h}

/-- Scale positions, NOT canonical test-measure `Spout`. -/
def pointStep (A: Levels G)(Ñ:ChartRatio G)(m N h k:ℕ)(Y:Era G ℝ): Era G ℝ:= ((A.S.block m).val:ℝ)^h • verseI A Ñ m N k Y
lemma nextStep (g:G.Simple)(p:m<N)(q:LocalRatio Ñ){Y:Era G ℝ}(hp:Auth k Y): Auth k (pointStep A Ñ m N h k Y):= (Auth.verse A p g q hp).μ _
lemma step_rise (g:G.Simple)(p:m<N)(q:LocalRatio Ñ){Y:Era G ℝ}(hp:Auth k Y) (v:k≤l): pointStep A Ñ m N h k Y=pointStep A Ñ m N h l Y:=by unfold pointStep; rw [verseExpand A p g q hp v]
lemma step_sub (g:G.Simple)(p:m<N)(q:LocalRatio Ñ)(a b:Era G ℝ)(hv:Auth k a)(hw:Auth k b): pointStep A Ñ m N h k (a-b)=pointStep A Ñ m N h k a-pointStep A Ñ m N h k b:=by unfold pointStep; rw [verse_lin A g p q hv hw,smul_sub]
lemma step_sum {J:Type*}(g:G.Simple)(p:m<N)(q:LocalRatio Ñ)(S:Finset J)(a:J→Era G ℝ)(hp:∀ i∈S,Auth k (a i))(c:J→ℝ): pointStep A Ñ m N h k (∑ i∈S,c i • a i)=∑ i∈S,c i • pointStep A Ñ m N h k (a i):=by unfold pointStep; rw [verse_sum A g p q hp c,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm ..
lemma step_μ (g:G.Simple)(p:m<N)(q:LocalRatio Ñ)(a:Era G ℝ)(hv:Auth k a) (c:ℝ): pointStep A Ñ m N h k (c • a)=c • pointStep A Ñ m N h k a:=by simpa using step_sum (h:=h) (A:=A) g p q {()} (fun _=>a) (fun i _=>hv) (fun _=>c)

def trim (c:Cost)(X:Era G ℝ): Era G ℝ:=(fun n=>affix c (X.1 n), affix c X.2)
lemma trim_auth (c:Cost){X: Era G ℝ}(p:Auth k X): Auth k (trim c X):=by
    have ht n:shellK k ((trim c X).1 n):= affix_shell c _ (p.span n)
    refine ⟨fun i j=>?_, ht,fun i=>aspire c _ (p.pale i), fun n=> certify (ι:=Unit) (fun _=>LinearMap.id) (fun _ _ f=> f ()) _ (ht n) (fun _=>?_)⟩
    · dsimp only [trim]; simp only [affix, Finset.sum_apply,Pi.smul_apply]; exact anzas (P:=fun (d:ℕ×ℕ) n=>coeff d.1 c • X.1 n d.2 j) _ (fun i _=> Soil.Bends.μ (p.wing ..) _)
    intro Z I x V V' v; change train _ (flash (affix c (X.1 n)))=train _ (flash (affix _ _)); rw [sponsor _ _ (p.span n),map_mul,map_mul,income,income,p.safe _ v]
lemma step_composed (g:G.Simple)(p:m<N)(q:LocalRatio Ñ)(c:Cost)(X: Era G ℝ)(hp:Auth k X): verseI A Ñ m N k (trim c X)=trim (Bank.reel (ratioHigh A Ñ N m) c) (verseI A Ñ m N k X):=by
    apply Auth.ext (Auth.verse A p g q (trim_auth _ hp)) (trim_auth _ (Auth.verse A p g q hp)); funext n
    let L:= ll A m; let K:= A.clock.kernel; let S:=stepAt L K n; let F:=xree L K n; let t:= n*L.L; let B:= freeForms A N (m+1); let P:=roam A N m n; let z:= (story A Ñ N (m+1)).1 t; let R:= reed S F B P Ñ z k (R:=ℝ); let V:= ratioHigh A Ñ N m
    change Blue.mix V (R (affix c (X.1 t)))=affix (Bank.reel V c) (Blue.mix V (R (X.1 t))); have hx:= (old A Ñ g q N (m+1) p).basis t
    rw [show R _= _ from reedDear S F Ñ B P z (X.1 t) k c q (A.blocks m 0).branches (age_sym ..) (hp.span _) (hp.pale _) hx.lamp hx.shape]
    exact mixedAff V c (R (X.1 t)) (reed_band S F B P k hx.lamp q (hp.span t)) (reed_smooth S F B P k Ñ z (hp.pale t))
lemma trim_μ (a:ℝ)(c:Cost)(X: Era G ℝ): trim c (a • X)= a • trim c X:=by
    have h (U:Type)(P:Pal ℝ U): affix c (a • P)= a • affix c P:=by funext i; unfold affix; rw [Pi.smul_apply,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm ((coeff i.1) c) a (P i.2)
    exact Prod.ext (funext fun n=> h (Woods G n) _) (h _ _)
lemma next_composed (g:G.Simple)(p:m<N)(q:LocalRatio Ñ)(c:Cost)(X: Era G ℝ)(hp:Auth k X):
    pointStep A Ñ m N h k (trim c X)=trim (Bank.reel (ratioHigh A Ñ N m) c) (pointStep A Ñ m N h k X):=by unfold pointStep; rw [step_composed g p q c X hp,trim_μ]

abbrev Needle (c:Cost)(e:ℕ): Prop:= coeff e c=1 ∧ ∀ i<e,coeff i c=0
lemma thin (e:ℕ) : Needle (PowerSeries.X^e) e:=⟨by simp,fun i h=> coeff_X_pow (R:=ℝ) _ _ |>.trans (if_neg (by omega))⟩
lemma Needle.spike (g:G.Simple)(p:m<N)(q:LocalRatio Ñ){x:Cost}(v:Needle x e): Needle (Bank.reel (ratioHigh A Ñ N m) x) e:=by
    let T:= ratioHigh A Ñ N m; have hc: coeff 0 T=1:=by rw [coeff_zero_eq_constantCoeff_apply]; exact back_cc (angle_tilt g q p)
    constructor
    · rw [reelQuote,Finset.sum_eq_single e]; swap; · intro i hi h; rw [v.2 i (by have he:=Finset.mem_range.mp hi; omega), zero_mul]
      swap; · simp
      rw [Nat.sub_self,v.1,one_mul,coeff_zero_eq_constantCoeff_apply,map_pow,← coeff_zero_eq_constantCoeff_apply,hc,one_pow]
    intro i h; rw [reelQuote]; exact Finset.sum_eq_zero fun i' hi=> by rw [v.2 i' (by have he:=Finset.mem_range.mp hi; omega),zero_mul]
lemma Needle.lance {x:Cost}(v:Needle x e)(P:Era G ℝ): (trim x P).2 e=P.2 0:=by
    change affix x P.2 e=P.2 0; rw [affix, Finset.sum_eq_single_of_mem (e,0)]; swap; · simp
    · rw [v.1,one_smul]
    intro i hi h; rw [v.2 i.1 ?_,zero_smul]; have hv:=Finset.mem_antidiagonal.mp hi; by_contra! H; exact h (Prod.ext (by change _= e; omega) (by change _= 0; omega))
lemma Needle.zero {x:Cost}(v:Needle x e)(p:i<e)(Y:Era G ℝ): (trim x Y).2 i=0:=by
    change affix x Y.2 i=0; unfold affix; refine Finset.sum_eq_zero fun i hi=>?_ ; rw [v.2 i.1 (by have he:=Finset.mem_antidiagonal.mp hi; omega),zero_smul]

def Probe (T:SectionData F)(D:ℕ)(w:h<D)(i:F.Index): Era G ℝ:=
    tuftV (out D) (vein ((fun n i=> herald T w i n),anthem T w) (seat F i))
lemma probed (H:Hol G)(T:SectionData F)(D:ℕ)(w:h<D)(i:F.Index)(q:T.Sound H)(p:Bid.pop T):
    Auth (F.grades i).2 (Probe T D w i):= (On_auth (hailed _ (freshly T H w q p) (seat F i) le_rfl)).tuft _
lemma emits (T:SectionData F)(D:ℕ)(w:h<D)(i:F.Index)(j r:ℕ)(lit:(F.grades i).2+j=r):
    (Probe T D w i).2 j r=floatA T i r:=by
    subst r; let I:=seat F i; have h:(F.grades i).2=valence F I:=rfl
    rw [h]; funext x; change out D (anthem T w I j (valence F I + j) _) = _; rw [anthem,shine_lit]
    change floatA T i _ _ • ((jewelBloom w I) (brow F I D))=_; rw [packBloom,if_pos rfl,smul_eq_mul,mul_one]
lemma direct (H:Hol G)(T:SectionData F)(D:ℕ)(w:h<D)(q:T.Sound H)(p:Bid.pop T)(i j: TagIx F r):
    row F ((Probe T D w i.val).2 0 r) j= if i=j then 1 else 0:=by
    rw [emits T _ w _ _ _ (by rw [Nat.add_zero,i.property])]; unfold row; let x:= (seat F i); let y:= seat F j
    have hv: valence F x=r:= i.property; have hz:valence F y=r:= j.property
    have hx:= cornerRead T (Nat.lt_succ_self h) y x H q p 0
    rw [g_lone,hz,anthem,add_zero,hv, shine_lit,if_pos rfl] at hx
    have hu:arret (brow F y _) (wire (h+1) ∘ floatA T i r) h r= arret (brow F y (h+1)) (carte T (Nat.lt_succ_self _) x r) h r:=by
        unfold arret; refine tsum_congr fun v=>?_ ; rw [shrubbery,if_pos (show notar F x= notar F y from rfl)]; change ((floatA T i r v)*eye (h+1) (page (h+1) (testa (h+1) 0))) • _= floatA T i r v • _; rw [eye_wall,if_pos rfl,mul_one]
    change echoS F _ y= if i=j then 1 else 0; unfold echoS trellis; rw [hz,hu]
    unfold echoS trellis at hx; rw [hz] at hx; refine hx.trans ?_ ; by_cases h:i=j
    · subst j; rw [if_pos (show y=x from rfl), if_pos rfl]
    rw [if_neg (fun v:y=x => h (Subtype.ext (congr_arg (sheet F) v.symm))),if_neg h]
end YM.WilsonCoeffUV.Mer.Xa
