import YM.Contacts.Procession.Polar
noncomputable section
namespace YM.Contacts.Procession.Lotus
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide Barrage Slope House
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch
set_option autoImplicit false
variable {X Y A B ι κ α β: Type}{f m:Side} {G:Gauge}{n k i r l p:ℕ}{b c d:ℝ}
open Hinges
lemma pack_seq (E:House X)(p:X→Y)(q:Y→A)(h:∀ i j, Summable (E i j)): plead (plead E p) q=plead E (q∘p):= funext fun i=>funext fun j=> pack_twice _ (h i j)
section arithmetic
variable (z : Site f)
def sack (z:Site f)(x: Co f X):Co f X:=(x.1+z,x.2)
def malt [Fintype X] : House.Dir (Co f X)→L[ℝ] House.Dir (Co f X) := ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (sack z i)
def walls (G:Gauge): Swatch G f →L[ℝ] Swatch G f:= (malt z).prodMap (malt z)
lemma still_mark (u:G.El)(x:Link G f): malt z (stain u x)=stain u (malt z x):=rfl
lemma phase_mark (v:Swatch G f): moveField (walls z G v)=malt z (moveField v):= by
   have he : shiftLinks (walls z G v)= (shiftLinks v) ∘ (sack z (X:=Axis)):= by
      funext u; rcases u with ⟨x,i⟩; let f':=switchSite v.1; change _=f' _* _*(f' _)⁻¹; change f' (x+z)* input G f v.2 (x+z,i) * (f' ((x+step i)+z))⁻¹= _ *(input G f v.2 _) * (f' ((x+z)+step i))⁻¹; rw [add_right_comm]; rfl
   unfold moveField; rw [he]; rfl
lemma scent [Fintype X](H: House (Co f X)) (i x):wind (plead H (sack z)) k i x=wind H k i (malt z x):= by
   unfold wind; refine sum_congr rfl fun j _=>?_ ; unfold House.grate; split; · unfold plead; rw [design_at,design_at,say_fold Summable.of_finite]; rfl
   rfl
lemma said {P:House (Lines G f 1)}(h:sealedL P k): sealedL (plead P (sack z)) k:= by
   intro i hi; let Q:= wind (plead P (sack z)) k i; let U:=wind P k i; have hk (x): Q x=U (malt z x):= scent z P i _; let hp:=h i hi; refine ⟨continuous_iff_continuousAt.mpr (fun _=> (wind_ana ..).continuousAt),wind_ana ..,fun x v=>?_,?_ ⟩
   · change Q _=Q v; rw [hk,hk,still_mark z]; apply hp.color
   let T:= U ∘ moveField; let A:Swatch G f→ℝ:= U ∘ Prod.snd; have hl:AnalyticAt ℝ A 0:=(hp.analytic).comp (f:= Prod.snd) contDiffAt_snd.analyticAt; have he:AnalyticAt ℝ T 0:=AnalyticAt.comp (f:=moveField) (g:=U) (moveField_zero (G:=G) (m:=f)|>.symm ▸ hp.analytic) moveField_analytic
   change Rays _ (fun z:Swatch G f=> Q _-Q _); rw [show (fun x:Swatch G f=> Q (moveField x)-Q x.2)=(T-A) ∘ walls z G from funext fun x=> by rw [hk,hk,← phase_mark z]; rfl]; exact merkin (he.sub hl) hp.grade _ ((walls z G).analyticAt _) (map_zero _)
lemma wisen (V:House (Lines G f 1))(h:Nation G f p V): Nation G f p (plead V (sack z)):= by
   refine ⟨⟨fun i j=> poetic _ (h.proper.sym i j) _,fun i j he=>?_⟩,fun k=>?_⟩; simp_rw [plead,h.proper.thin _ _ ‹_›]; ext; simp [packing,cram]; rw [← pledge_shift]; apply said _ (h.birth k)
end arithmetic
variable {F: bore G}{U:TableFee}{x:Dye G}{σ:ℝ≥0}
abbrev parcelY (σ:ℝ≥0)(a:Cover):= Real.exp ((σ:ℝ)*(Laurent.size a:ℝ))
abbrev migrated (F:House (Node X))(a:Cover):= plead F (backpack a)
lemma liftedRide (u:Cover) (x:Node X):lower f (backpack u x)=sack (wrap f u) (lower f x):= Prod.ext (map_add ..) rfl
lemma overview (z:Cover)(m:Side)(F:House (Node X))(h:∀ i j, Summable (F i j)): plead (migrated F z) (lower m)= plead (plead F (lower m)) (sack (wrap m z)):= by rw [migrated,pack_seq _ _ _ h,pack_seq _ _ _ h]; congr 1; exact funext (liftedRide z)
lemma migrant (z:Cover) (hp:Mount F p)(hb:Price F x σ U): Mount (migrated F z) p:= ⟨properB p _ _ hp.incarnate, fun m=>by rw [overview z m F (fun i j=>(hb.lands i j).summ)]; exact wisen _ _ (hp.attends _)⟩
lemma terrain_free {X:Type}(x y: Node X)(z:Cover) : (terrain σ X).step (backpack z x) (backpack z y)=(terrain σ X).step x y:= by
   simp only [terrain_step]; congr 2; change (size (y.1+z-(x.1+z)):ℝ) = _; rw [add_sub_add_right_eq_sub]
lemma staple [Fintype ι]{P:Field ι (Node X)}{x:X}(u:Cover)(h:Rest (terrain σ _) (0,x) P b) : Rest (terrain σ _) (0,x) (packing (backpack u) P) (parcelY σ u*b):= by
   let t:=terrain σ X; let y:=( (0:Cover),x); let z:= backpack u y; have hv:1≤ parcelY σ u:=Real.one_le_exp (by positivity); refine pack_cost _ (backpack u).injective h (zero_le_one.trans hv) (fun v=>?_); let X (i: Option ι): Node X:= i.elim y v; let Z:= backpack u ∘ X; let Y(i: Option ι):Node _:= i.elim y (fun i=>Z (some i)); let w:=fee t y v; have hx:1≤w:= fee_one _; let V:=parcelY σ u*w; change t.bill Y ≤ V; have he : 1 ≤ V:= one_le_mul_of_one_le_of_one_le hv hx; have hW i:t.step y (Z (some i)) ≤ V:= by
      have hp:t.step y z=parcelY σ u:= by rw [terrain_step]; congr; change 0+u-0=u; rw [zero_add,sub_zero]
      apply (t.triangle _ z _).trans; rw [hp,show t.step z (Z (some i))=t.step y (v i) from terrain_free (σ:=σ) _ (v i) u]; exact mul_le_mul_of_nonneg_left (fee_leg v i) (Real.exp_pos _).le
   apply t.wide _ he; rintro (_|i) (_|j); · exact le_trans (b:=1) (congr_arg ( (↑):ℝ≥0→ℝ) (t.flat _) |>.le) he
   · exact hW j
   · unfold Pulse.Range.step; rw [t.mirror]; exact hW i
   exact (terrain_free (v i) (v j) u).le.trans ((t.width X (some i) (some j)).trans (le_mul_of_one_le_left (zero_le_one.trans hx) hv)) -- letX shadows type
lemma revised (z:Cover)(hf:Price F x σ U): Price (migrated F z) x σ (fun i j=> parcelY σ z*U i j):=⟨fun i j=> staple z (hf.lands ..)⟩
lemma orchid (P:Cross f X Y)(F:Field (Fin n) (Node X))(z:Cover): printRun (Shuttle.Trace.wreath z (install P) F)=lifts P (packing (backpack z) F):= by
   unfold lifts hoist; apply congr_arg; funext i; unfold Trace.wreath allAt; let u:= backpack (α:=X) z; let e:= Equiv.arrowCongr (Equiv.refl (Fin n)) u; rw [← e.tsum_eq (fun x=>packing u F x * (∏ j, install P (x j) (i j)))]; apply tsum_congr; intro x; change _= packing _ _ (u∘x)* _; rw [pack_io _ x u.injective]; rfl
lemma coil_burst {F: House (Node X)} (p i k:ℕ)(a:Cover): coil (migrated F a) p i k=packing (backpack a) (coil F p i k):= (Catch.coil_pack F _ _ _ _).symm
end YM.Contacts.Procession.Lotus
