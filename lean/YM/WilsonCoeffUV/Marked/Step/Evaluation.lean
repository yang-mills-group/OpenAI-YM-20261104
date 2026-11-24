import YM.WilsonCoeffUV.Marked.Step.JointTaps
/-!
# Mixed full Step on all covers (root labels never diluting).
 -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08
open scoped Topology BigOperators
variable {c f:Side}{ι α U:Type}{J K I S T:Finset ι}{D k:ι→ℕ}{i j e r h N n m l:ℕ}{G:Gauge}
variable [DecidableEq ι]

def SubC (K:ropes Cover α α)(V:thalamus D (Cloth α))(i e:ℕ)(S:Finset ι): Gen (Pen D S) (Cloth α):= ∑ J∈S.powerset, if v:J⊆ S then Sewing K v (V J) (V (S\J)) i e else 0
lemma subSam (K:ropes Cover α α){V W:thalamus D (Cloth α)}(h:∀ X i',i' ≤ i →∀ j', V X i' j'=W X i' j')(e:ℕ)(S:Finset ι) : SubC K V i e S= SubC K W i e S:=by
    refine Finset.sum_congr rfl fun j g=>?_ ; have hg:=Finset.mem_powerset.mp g; rw [dif_pos hg,dif_pos hg]; unfold Sewing; refine Finset.sum_congr rfl fun k v=> ?_; have hv:= Finset.mem_antidiagonal.mp v; refine Finset.sum_congr rfl fun l z=>?_ ; rw [h j _ (by omega),h _ _ (by omega)]

def Sat (K:ropes Cover α α)(R:Layers ℝ (Cloth α))(V:thalamus D (Cloth α))(i e:ℕ)(S:Finset ι): Gen (Pen D S) (Cloth α):= rime K (V S i e)+Soil.paintC K R (V S) i e + Soil.paintC K.transpose R (V S) i e +SubC K V i e S
lemma satH (K:ropes Cover α α)(R:Layers ℝ (Cloth α)){V W:thalamus D (Cloth α)}(h:∀ X i',i' ≤ i →∀ j', V X i' j'=W X i' j')(e:ℕ)(S:Finset ι): Sat K R V i e S=Sat K R W i e S:=by
    have he K: Soil.paintC K R (V S) i e=Soil.paintC K R (W S) i e:= by
        unfold Soil.paintC; apply Finset.sum_congr rfl; intro j hj; have hv:=Finset.mem_antidiagonal.mp hj; refine Finset.sum_congr rfl fun l hl=>?_ ; rw [h S _ (by omega)]
    unfold Sat; rw [h S _ le_rfl, he,he,subSam K h]

noncomputable def Temple (X:ropes Cover α α)(V:Layers ℝ (Cloth α))(L:(S:Finset ι)→ Pal (Pen D S) (Cloth α))(S:Finset ι)(j i:ℕ): Gen (Pen D S) (Cloth α):= match j with
    | 0=> L S i
    | n+1=> ((n+1:ℕ):ℝ)⁻¹ • Sat X V (fun S b i=> if _h:b≤n then Temple X V L S b i else 0) n i S
termination_by j
lemma warmUp (X:ropes Cover α α)(V:Layers ℝ (Cloth α))(L:(S:Finset ι)→ Pal (Pen D S) (Cloth α))(S:Finset ι)(j i:ℕ): Temple X V L S (j+1) i=((j+1:ℕ):ℝ)⁻¹ • Sat X V (Temple X V L) j i S:=by rw [Temple,satH _ _ (fun S b v e=>dif_pos (show b≤ j from v))]

def Humour (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G)(Γ:ropes Cover (Larvae G P.L) (Larvae G P.L))(M:ropes Cover (Larvae G P.L) (Hooks G))(W:Bank.Canvas G)(Q:family G D):=Temple (stair (β:=Hooks G) (upper (β:=Hooks G) Γ 0) 0) (spurs P K Ñ Γ M W) (fun S=>slidesJ P M (Q S).2)
section
variable (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G){H:FaceRow}{Q:(n:Side)→Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ}{Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)}{M:ropes Cover (Larvae G P.L) (Hooks G)}{W:Bank.Canvas G}
lemma humourCast (Y:family G D)(w:Y ∅=0)(hx:Eu k Y)(b:P.Branches K G)(t:LocalRatio Ñ)(g:PaintKit P K G H Q Γ M){F:Crude G}(v:∀ n,Interlace H (F n))(f:∀ i r,Yields (fun n=> F n i r) (W i r))(S i j r):
     Bends 0 (fun n=> bend (weaveH (ratioN P.L n) G) (inHeat (stepAt P K n) (xree P K n) H (Q n) Ñ (F (n*P.L)) Y S i j) r) (Humour P K Ñ Γ M W Y S i j r):=by
    let O (n:Side):= xree P K n; let s (n:Side):= stepAt P K n; let I n:= weaveFine (ratioN P.L n) G; let T n:= weaveH (ratioN P.L n) G; let R (n:Side):= teller G P K Q n; let Z (n:Side):= F (n*P.L); let U (n:Side) := fillSlots (Woods G n) (mer P K H n (G:=G)); let d n:=xray (s n) (O n) H (Q n) Ñ (Z n); let u (n:Side) := allotM (T n) (T n) (U n); let V':= stair (α:=Larvae G P.L) (β:=Hooks G) (upper (β:=Hooks G) Γ 0) 0
    let A (n:Side):=inHeat (s n) (O n) H (Q n) Ñ (Z n) Y; let C:=Humour P K Ñ Γ M W Y; let X (n:Side)(S:Finset ι) i j:=bend (T n) (A n S i j); let T' n j k:=bend (T n) (d n j k); let R':=spurs P K Ñ Γ M W
    have ht : Pilots u V':=by
        rw [show u=fun n:Side=> stair (upper (allotM (I n) (I n) (mer P K H n (G:=G))) (β:=Hooks G) 0) (β:=Hooks G) 0 from funext fun n=>lamp_chart ..]; exact ((g.toll.deck (Pilots.silent (β:=Hooks G))).deck' (Pilots.silent (α:=Hooks G)))
    have hv a j r:Yields (fun n=> T' n a j r) (R' a j r):=spurs_enter P K Ñ H F Q b t f g a j r
    change Bends 0 (fun n=> X n S i j r) (C S i j r)
    induction i using Nat.strong_induction_on generalizing S j r with
    | h i ih=>
      cases i with
      | zero=>
          have hφ:Bends (lift (0:Site P.L)) (fun n=> (Y S).1 n j r) ((Y S).2 j r):= by rw [coat0]; exact (hx S).wing j r
          unfold C Humour; rw [Temple]; apply Bends.congr (solo_flash (P:=tiles P.L ((Y S).2 j)) (Q:=fun n=>bend (I n) ((Y S).1 (n*P.L) j)) (Pilots.one.deck g.mark) (hφ.ciphers 0))
          refine Eventually.of_forall fun n=>?_ ; unfold X A; have hZ: Interlace H (Z n):=v _; rw [coldE _ _ H _ Ñ (Z n) Y hZ.lamp t hx w S, srCold,bend_fade (I n) (T n), show allotM (I n) (T n) _=upper 1 _ from cam_chart _ _]
      | succ i=>
         have hX (n:Side): X n S (i+1) j= ((i+1:ℕ):ℝ)⁻¹ • (ripple (u n) (X n S i j)+ravel (u n) (T' n) (X n S) i j+ravel (u n).transpose (T' n) (X n S) i j+∑ J∈S.powerset, if v:J⊆ S then sewsV (u n) v (X n J) (X n (S\J)) i j else 0):=by
             have ht:=v (n*P.L); have hv:=outerS (s n) (O n) H (Q n) Ñ (Z n) Y ht.lamp t hx ht.shape b i j S
             change bend (T n) _= _; unfold X A; dsimp only at hv; rw [hv,bend_smul (W:=Pen D S) (T n),bend_add,bend_add,bend_add,bend_ripple,bend_ravel, bend_ravel,bend_sum]; apply congr_arg (((i+1:ℕ):ℝ)⁻¹ • ·); apply congr_arg₂ (·+·) rfl; apply Finset.sum_congr rfl; intro a ha; have H:= Finset.mem_powerset.mp ha; rw [dif_pos H,dif_pos H]; exact bendSean ..
         have he: C S (i+1) j=((i+1:ℕ):ℝ)⁻¹ • Sat V' R' C i j S:=warmUp ..
         rw [he]; simp_rw [hX]
         let ha {M Z} (z:Pilots M (Z:ropes Cover (Hinge G P.L) (Hinge G P.L))):= spans_bracket (P:=fun n=>X n S) (R:=C S) (Q:=T') z (v:=i) (e:=j) (fun _ _ _ _ _=>hv ..) (fun x p j _ r=> ih x (by omega) ..) r
         let H' (n:Side):=∑ J∈S.powerset, if v:J⊆ S then sewsV (u n) v (X n J) (X n (S\J)) i j else 0
         have hI:Bends 0 (fun n=>H' n r) (SubC V' C i j S r):=by
             apply leaderT; intro a e; have ht':= Finset.mem_powerset.mp e; simp_rw [dif_pos ht']; exact roseQ ht' ht (fun x l j _ r=> ih x (by omega) a j r) (fun x l j _ r=> ih x (by omega) _ j r) r
         have hg:= ih i i.lt_succ_self S j (r+2)
         exact ((((rime_period (P:=C S i j) (Q:=fun n=>X n S i j) ht hg).add (ha ht)).add (ha (capit ht))).add hI).μ _
end

variable (A:Levels G)(Ñ:ChartRatio G)(m N:ℕ)(K:family G D)
abbrev abode := Humour (ll A m) A.clock.kernel Ñ (shuttleM (conditional A N m)) (shuttleM (feedA A N m)) (actionW A Ñ N (m+1)) K
lemma onSide (k)(p:K ∅=0)(h:Eu k K)(v:G.Simple)(x:LocalRatio Ñ)(f:m<N)(S):
      (logO A Ñ m N K k S).2=Blue.mix (ratioHigh A Ñ N m) (fun i=> sluice (finalZ (abode A Ñ m N K S) (mass k S) i)):=by
   let Y:= logO A Ñ m N K k; let P:= ll A m; let B:=A.clock.kernel; let L(n:Side):= stepAt P B n; let F (n:Side):= xree P B n
   let Q (n:Side):=roam A N m n; let W:=(story A Ñ N (m+1)).1; let H:=freeForms A N (m+1); let X (n:Side):=inHeat (L n) (F n) H (Q n) Ñ (W (n*P.L)) K; let C:=abode A Ñ m N K; let T:=ratioHigh A Ñ N m; let J:=mass k S
   have hu:=old A Ñ v x N (m+1) f
   have hp (i r t : ℕ): Bends 0 (fun n=>bend (weaveH (ratioN P.L n) G) (X n S i r) t) (C S i r t):= humourCast P B Ñ K p h (A.blocks m 0).branches x (resin A N m f) hu.basis hu.patch S i r t
   let M (n:Side) i:= fade plug (finalZ (X n S) J i)
   have ht i r: Bends 0 (fun n=> M n i r) (sluice (finalZ (C S) J i) r):=by
      refine (leaderT (s:=Finset.range (1+J+3*i)) (P:=fun n j=> bend (weaveH (ratioN P.L n) G) (X n S j i)) (F:=fun j=> C S j i) (fun j _=> hp j i r)).scooped.congr (Eventually.of_forall fun n=>?_)
      unfold M finalZ; rw [into_shade (ratioN P.L n), bend_sum]; rfl
   funext i r; refine ((step_L A Ñ m N K k f v x h S).wing i r).exten ((bend_mixX (P:=M) ht T i r).congr (Eventually.of_forall fun n=>?_)); rw [feeleg _ _ _ _ _ _ f v x h]; rfl
end YM.WilsonCoeffUV.Wheel.Mark
