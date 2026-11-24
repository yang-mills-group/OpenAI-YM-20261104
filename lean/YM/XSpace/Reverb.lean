import YM.XSpace.Stylus

/-! # Vacuum covariance announcements pulled through the real line tariffs -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Trace
open Scale Lattice Sail Litter Chart2 Further.FreeCovariance.KP Function Filter Finsupp MvPolynomial Outline Next.Rank.Normal Contraction
open scoped Topology BigOperators InnerProductSpace
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F] {G:Gauge}

-- recover charges from finite-file samples
lemma ticket (v:Line G)(i:UnitIndex G): ram i (deposit v)=v i:=by
  let L: Line G→ₗ[ℝ] ℝ:= ram i ∘ₗ deposit; change L v=v i; suffices L= Finsupp.lapply i from LinearMap.congr_fun this v; apply line_eq; intro j; simp [L,deposited,dotter, needle, deposit,Finsupp.single_apply, eq_comm]
lemma launched (v:Line G)(i:UnitIndex G): probe v (crumb i)= v i:=by
  apply LinearMap.congr_fun (f:=probe.flip (crumb i)) (g:=Finsupp.lapply i) ?_; apply line_eq; intro j; simp [probe, dotter,LinearMap.flip_apply, needle, Finsupp.single_apply, eq_comm]
lemma inquire : Injective (probe (G:=G)):=fun v u h=> Finsupp.ext fun i=> by rw [← launched, ← launched,h]
def handshake (L M: Line G): ℝ := probe L (bake M)
def complexCode (G:Gauge) := linearCombination ℝ (fun i:UnitIndex G=> single i (1:ℂ))
def harp (L:Line G):=glyph (complexCode G L)
lemma crest (i:UnitIndex G): complexCode G (needle i)=single i (1:ℂ):=by rw [complexCode,needle,linearCombination_single,one_smul]
lemma harps (i:UnitIndex G): harp (needle i)=X i:=by rw [harp,crest,glyph,linearCombination_single,one_smul]
lemma leg_test (L:Line G)(A: Contact G): pit A (harp L)=(↑(probe L A):ℂ):=by
  let g:= ((pit A).toLinearMap ∘ₗ (glyph (V:=UnitIndex G))).restrictScalars ℝ; apply LinearMap.congr_fun (f:=g ∘ₗ complexCode G) (g:= Complex.ofRealLI.toLinearMap ∘ₗ probe.flip A) ?_; apply line_eq; intro x; change pit A (harp (needle x))= (↑(probe (needle x) A):ℂ); rw [harps,probes]; exact aeval_X ..
lemma wave_nat (L:Line G)(A:Contact G): linearCombination ℂ (numbers A) (complexCode G L)=(↑(probe L A):ℂ):=by
  have he:= reads_at (Z:=UnitIndex G) (fun _:Unit=> complexCode G L) (numbers A) (); rw [exchange_x] at he; exact he.symm.trans (leg_test L A)
lemma played (v:Line G)(A: Contact G): D A (harp v) = C ((probe v A:ℝ):ℂ):=by
  have he:= exchange_slit (Z:=UnitIndex G) (fun _:Unit=> complexCode G v) (numbers A) (X ()); simp only [exchange_x, slit_X,exchange_c,reads,wave_nat] at he; exact he
lemma reveal (L:Line G): linearCombination ℂ (duskCov G).cov (complexCode G L)= numbers (bake L):=by
  let g:= (linearCombination ℂ (duskCov G).cov).restrictScalars ℝ; funext q
  apply LinearMap.congr_fun (f:=LinearMap.proj q ∘ₗ g ∘ₗ complexCode G) (g:=Complex.ofRealLI.toLinearMap ∘ₗ ram q ∘ₗ bake) ?_; apply line_eq; intro p; change linearCombination ℂ (duskCov G).cov _ q= ↑(ram q (bake _)); rw [crest,linearCombination_single,one_smul,baked]; rw [rot,beads,beaded]
lemma heard (L M:Line G): treats (duskCov G) (complexCode G L) (complexCode G M)=(handshake L M:ℂ):=by rw [treats_comm,treats,reveal,wave_nat];rfl
lemma listening (L M:Line G): handshake L M=handshake M L:= by apply Complex.ofReal_injective; rw [← heard,← heard,treats_comm]
-- support movement

def sweep (x:Cover): Module.End ℝ (Cover→F):= LinearMap.pi fun i=> LinearMap.proj (x+i)
def zone (x:Cover): Module.End ℝ (Tape F):=LinearMap.pi fun i=> LinearMap.proj (x+i.1,i.2)
def radius (x:Cover) (i:UnitIndex G):UnitIndex G:=((x+i.1.1,i.1.2),i.2)
def displace (x:Cover): Module.End ℝ (Line G):= linearCombination ℝ fun i=>needle (G:=G) (radius x i)
lemma pin (x:Cover)(p:UnitIndex G): displace x (needle p)=needle (radius x p):=by rw [displace,needle,linearCombination_single,one_smul]
lemma zone_ap (x:Cover)(p:Tape F)(e): zone x p e=p (x+e.1,e.2):=rfl
lemma born (x:Cover)(v:Line G)(A:Contact G): probe (displace x v) A= probe v (zone x A):=by
  apply LinearMap.congr_fun (f:=probe.flip A ∘ₗ displace x) (g:=probe.flip (zone x A)) ?_; apply line_eq; intro p; rw [LinearMap.comp_apply,pin]; change probe _ A= probe _ (zone x A); rw [probes,probes];rfl
lemma slid_bake (x:Cover)(v:Line G):bake (displace x v)=zone (-x) (bake v):=by
  apply LinearMap.congr_fun (f:=bake ∘ₗ displace x) (g:=zone (-x) ∘ₗ bake) ?_; apply line_eq; intro p; simp only [LinearMap.comp_apply,pin,baked]; funext i; unfold φ; simp only [radius,zone_ap]; rw [show i.1-(x+p.1.1)= -x+i.1-p.1.1 by abel]
lemma zone_add (x y:Cover)(p:Tape F): zone x (zone y p)=zone (x+y) p:= by funext i; simp_rw [zone_ap]; rw [show y+(x+i.1)=(x+y)+i.1 by abel]
lemma displacement (x y: Cover)(p: Line G): displace x (displace y p)=displace (x+y) p:= by apply inquire; ext1 z; simp_rw [born,zone_add y,add_comm y]
lemma originate (v:Line G): displace 0 v=v:=by apply inquire; ext1 y; rw [born]; congr 1; ext1 p; rw [zone_ap]; simp
lemma meter_serves (u v:Line G)(x:Cover):handshake (displace x u) (displace x v)=handshake u v:=by unfold handshake; rw [slid_bake,born,zone_add,add_neg_cancel]; congr 1; funext i; simp [zone_ap]
lemma twig_zone (x:Cover)(p:Tape F)(i:Axis): twig i (zone x p)=sweep x (twig i p):=rfl
lemma rat_sweep (x:Cover)(i:Axis)(p:Cover→F): rat i (sweep x p)=sweep x (rat i p):=by funext y; change p (x+(y-step i))-p (x+y)=p (x+y-step i)-p (x+y); rw [add_sub_assoc]
lemma tooth_sweep (x:Cover)(i:Axis)(p:Cover→F): teeth i (sweep x p)=sweep x (teeth i p):=by funext y; change p (x+(y+step i))-p (x+y)=p (x+y+step i)-p (x+y); rw [add_assoc]
lemma pressed (x:Cover)(A:Tape F):press (zone x A)=zone x (press A):=by
  funext i; obtain ⟨i,j⟩:= i; change twig j (press (zone x A)) i = twig j (zone x (press A)) i; rw [job, twig_zone, job]; unfold crackle; simp_rw [map_sum,LinearMap.sub_apply,LinearMap.comp_apply, map_sub,twig_zone,tooth_sweep,rat_sweep]

-- record moving split lemma when renaming Cover polynomials (motif read always at root zero)
def volume (x:Cover): St ℤ G→ₐ[ℂ] St ℤ G:= MvPolynomial.rename (radius x)
lemma ting (x:Cover)(A:Contact G)(p:St ℤ G):pit A (volume x p)=pit (zone x A) p:=by
  suffices h : (pit A).comp (volume x)=pit (zone x A) from DFunLike.congr_fun h p; ext1 i; rw [AlgHom.comp_apply,volume,MvPolynomial.rename_X,pit,pit,aeval_X,aeval_X];rfl
lemma rings (x:Cover)(v:Line G):volume x (harp v)=harp (displace x v):=by apply same; intro A; rw [ting,leg_test,leg_test,born]
lemma stained (x:Cover)(p:St ℤ G):volume x p = (Chart.lug x).pull p:=by unfold volume Chart.pull; rw [show radius (G:=G) x=(Chart.lug x).roll from funext fun i=>by unfold radius Chart.roll Chart.move Chart.lug; simp [add_comm x]; rfl]
lemma hop (x:Cover): scope (fun i:UnitIndex G=> single (radius x i) 1) (duskCov G)=duskCov G:=by
  apply Symmetric.ext; funext i j; rw [match_name]; change coal cover (radius x i) (radius x j)=coal _ _ _; simp [radius,coal]
lemma meant (x:Cover)(p:St ℤ G): milk (duskCov G) (volume x p)=volume x (milk (duskCov G) p):=by unfold volume; rw [labelled,prepared,hop]
end YM.XSpace.Trace
