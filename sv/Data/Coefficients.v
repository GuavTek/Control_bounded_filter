const real Lfr[0:2] = {0.9526408435505846, 0.97320481244078, 0.97320481244078};

const real Lfi[0:2] = {0.0, 0.07051980570136974, -0.07051980570136974};

const real Lbr[0:2] = {0.9526408435505846, 0.97320481244078, 0.97320481244078};

const real Lbi[0:2] = {0.0, 0.07051980570136974, -0.07051980570136974};

const real Wfr[0:2] = {-0.000633177960514777, 0.00038419980174515995, 0.00038419980174515995};

const real Wfi[0:2] = {-0.0, -0.0007604978272513302, 0.0007604978272513302};

const real Wbr[0:2] = {0.000633177960514777, -0.00038419980174515995, -0.00038419980174515995};

const real Wbi[0:2] = {0.0, 0.0007604978272513302, -0.0007604978272513302};

const real Ffr[0:2][0:59] = '{
	'{20.549783326922284, -1.9986035670700628, 0.3417449698305984, 19.576562923340983, -1.9039513880568322, 0.32556021633859034, 18.649433417112654, -1.813781856397767, 0.31014195911930553, 17.76621198221866, -1.727882677695514, 0.29545389755584617, 16.92481916943929, -1.6460516116362975, 0.2814614501979093, 16.12327401051575, -1.568095995837002, 0.2681316733435072, 15.359689354174943, -1.4938322922424556, 0.2554331834765885, 14.63226742303615, -1.4230856550049562, 0.2433360833779485, 13.9392955809389, -1.355689518828658, 0.2318118917354643, 13.279142300726571, -1.291485206809619, 0.2208334760879295, 12.65025332299241, -1.2303215568482164, 0.210374988944613, 12.051147996744076, -1.1720545657543535, 0.20041180693014105, 11.480415793371217, -1.1165470502075416, 0.1909204728114265, 10.93671298570861, -1.0636683237736293, 0.18187864027015377, 10.418759484376084, -1.0132938892177468, 0.17326502129079266, 9.925335823946686, -0.9653051453890468, 0.1650593360402707, 9.455280291847409, -0.9195891079871414, 0.1572422651213029, 9.007486193232733, -0.8760381435528001, 0.14979540408696268, 8.580899245391477, -0.8345497160566276, 0.14270122010940484, 8.17451509555231, -0.7950261454890866, 0.13594301070072107},
	'{-10.434437110710538, 1.0760923496837065, 0.06891711074802961, -9.881283969676142, 1.1405637001047084, 0.053582495228450495, -9.298391869753319, 1.1954559381298888, 0.038677458501671896, -8.69050254129909, 1.2409155039141384, 0.024266248960443652, -8.06227284872259, 1.277135504798331, 0.010407227158366929, -7.41825235317671, 1.304352381002729, -0.002847184297811084, -6.762862560647742, 1.3228424844230036, -0.01545051466277176, -6.10037789281319, 1.3329185941613548, -0.027362224428507713, -5.434908406443638, 1.334926391653283, -0.03854765193326715, -4.770384275938826, 1.329240917385493, -0.0489779290769246, -4.1105420428552515, 1.3162630302516094, -0.05862986810222621, -3.4589126260418195, 1.296415889569251, -0.06748582147216606, -2.818811076286206, 1.2701414786939313, -0.07553351692961269, -2.1933280502175245, 1.2378971880215195, -0.08276586986661993, -1.5853229696363167, 1.2001524739808105, -0.08918077515808404, -0.9974188244713829, 1.1573856093900825, -0.09478088062807172, -0.43199857021132493, 1.110080539295172, -0.0995733443178109, 0.10879693606121554, 1.0587238551300706, -0.10356957771262819, 0.6230695229845977, 1.0038018987526014, -0.10678497706169178, 1.1091628829706905, 0.945798006615248, -0.1092386448899734},
	'{-10.434437110710538, 1.0760923496837065, 0.06891711074802961, -9.881283969676142, 1.1405637001047084, 0.053582495228450495, -9.298391869753319, 1.1954559381298888, 0.038677458501671896, -8.69050254129909, 1.2409155039141384, 0.024266248960443652, -8.06227284872259, 1.277135504798331, 0.010407227158366929, -7.41825235317671, 1.304352381002729, -0.002847184297811084, -6.762862560647742, 1.3228424844230036, -0.01545051466277176, -6.10037789281319, 1.3329185941613546, -0.027362224428507713, -5.434908406443638, 1.334926391653283, -0.03854765193326715, -4.770384275938827, 1.3292409173854929, -0.0489779290769246, -4.110542042855252, 1.3162630302516094, -0.05862986810222621, -3.4589126260418195, 1.2964158895692508, -0.06748582147216606, -2.818811076286206, 1.2701414786939311, -0.07553351692961269, -2.1933280502175245, 1.2378971880215195, -0.08276586986661993, -1.5853229696363171, 1.2001524739808103, -0.08918077515808404, -0.9974188244713833, 1.1573856093900823, -0.09478088062807172, -0.43199857021132493, 1.1100805392951718, -0.0995733443178109, 0.10879693606121554, 1.0587238551300706, -0.10356957771262819, 0.6230695229845977, 1.0038018987526012, -0.10678497706169178, 1.10916288297069, 0.9457980066152478, -0.1092386448899734}};

const real Ffi[0:2][0:59] = '{
	'{5.002502244065731e-16, 2.2116604277464022e-16, -1.470080668687619e-18, 4.765587957650471e-16, 2.1069180555357794e-16, -1.400458888305981e-18, 4.539893731990653e-16, 2.0071361937175625e-16, -1.3341343367137236e-18, 4.324888194473587e-16, 1.9120799167040084e-16, -1.2709508599367614e-18, 4.120065137845283e-16, 1.821525424785038e-16, -1.2107596993214973e-18, 3.924942328400286e-16, 1.7352595172160557e-16, -1.1534191412986835e-18, 3.7390603706146445e-16, 1.6530790902598836e-16, -1.0987941837341688e-18, 3.561981625548896e-16, 1.5747906590010084e-16, -1.0467562180809946e-18, 3.3932891804745836e-16, 1.500209901806302e-16, -9.971827265844986e-19, 3.232585867298379e-16, 1.4291612263596952e-16, -9.499569938275287e-19, 3.0794933274728263e-16, 1.361477356249088e-16, -9.049678319366345e-19, 2.9336511211921094e-16, 1.296998937132151e-16, -8.621093188022591e-19, 2.79471587877557e-16, 1.2355741615537843e-16, -8.21280548696604e-19, 2.6623604922409725e-16, 1.1770584115319033e-16, -7.823853947020199e-19, 2.5362733451641897e-16, 1.1213139180700636e-16, -7.453322823905894e-19, 2.4161575790120765e-16, 1.0682094367952765e-16, -7.100339742220536e-19, 2.3017303942212033e-16, 1.0176199389573472e-16, -6.764073641524712e-19, 2.1927223843769069e-16, 9.694263170622216e-17, -6.443732819700377e-19, 2.088876901925066e-16, 9.235151044462915e-17, -6.138563068973955e-19, 1.9899494539232267e-16, 8.797782081314213e-17, -5.847845900215814e-19},
	'{-3.8792001602566697, -1.323109810553637, 0.19126497126443642, -4.511090742033305, -1.2117710116019829, 0.19100001174534786, -5.087041445125483, -1.0988690495458626, 0.18966075775932295, -5.60645400347202, -0.985121326778791, 0.1873062890410988, -6.06908056756652, -0.8712156958313233, 0.1839986330570126, -6.475008330249903, -0.7578079602042875, 0.17980227081070796, -6.8246429821830965, -0.6455196773023122, 0.17478365235728374, -7.118691147212733, -0.5349362615008024, 0.16901072431808, -7.3581419464531255, -0.4266053837656586, 0.16255247151020177, -7.5442478377376965, -0.3210356627288645, 0.15547847462329312, -7.678504874192352, -0.21869564070851077, 0.14785848569218038, -7.762632522103447, -0.12001303685210263, 0.13976202292897025, -7.798553174046867, -0.02537426837950707, 0.13125798629311797, -7.788371488466303, 0.06487577019164636, 0.12241429499393093, -7.734353681592671, 0.15043368093886184, 0.11329754793794, -7.638906891837724, 0.23103730152002622, 0.10397270795449756, -7.5045587306281245, 0.30646522198837106, 0.09450281045772045, -7.333937127126334, 0.3765360928287819, 0.08494869703230482, -7.129750567465516, 0.44110773815379656, 0.07536877426554539, -6.894768822060503, 0.5000760884388418, 0.06581879798877587},
	'{3.8792001602566692, 1.3231098105536367, -0.19126497126443642, 4.511090742033305, 1.2117710116019826, -0.19100001174534786, 5.087041445125482, 1.0988690495458624, -0.18966075775932295, 5.60645400347202, 0.9851213267787908, -0.1873062890410988, 6.06908056756652, 0.8712156958313231, -0.1839986330570126, 6.475008330249903, 0.7578079602042873, -0.17980227081070796, 6.824642982183096, 0.6455196773023122, -0.17478365235728374, 7.118691147212733, 0.5349362615008022, -0.16901072431808, 7.3581419464531255, 0.4266053837656584, -0.16255247151020177, 7.5442478377376965, 0.3210356627288644, -0.15547847462329312, 7.678504874192351, 0.21869564070851066, -0.14785848569218038, 7.762632522103447, 0.12001303685210252, -0.13976202292897025, 7.798553174046867, 0.02537426837950696, -0.13125798629311797, 7.788371488466302, -0.06487577019164648, -0.12241429499393093, 7.734353681592671, -0.15043368093886195, -0.11329754793794, 7.638906891837724, -0.23103730152002633, -0.10397270795449756, 7.5045587306281245, -0.3064652219883711, -0.09450281045772045, 7.333937127126334, -0.376536092828782, -0.08494869703230482, 7.129750567465516, -0.4411077381537966, -0.07536877426554539, 6.894768822060503, -0.5000760884388418, -0.06581879798877587}};

const real Fbr[0:2][0:59] = '{
	'{-20.549783326922284, -1.9986035670700628, -0.3417449698305984, -19.576562923340983, -1.9039513880568322, -0.32556021633859034, -18.649433417112654, -1.813781856397767, -0.31014195911930553, -17.76621198221866, -1.727882677695514, -0.29545389755584617, -16.92481916943929, -1.6460516116362975, -0.2814614501979093, -16.12327401051575, -1.568095995837002, -0.2681316733435072, -15.359689354174943, -1.4938322922424556, -0.2554331834765885, -14.63226742303615, -1.4230856550049562, -0.2433360833779485, -13.9392955809389, -1.355689518828658, -0.2318118917354643, -13.279142300726571, -1.291485206809619, -0.2208334760879295, -12.65025332299241, -1.2303215568482164, -0.210374988944613, -12.051147996744076, -1.1720545657543535, -0.20041180693014105, -11.480415793371217, -1.1165470502075416, -0.1909204728114265, -10.93671298570861, -1.0636683237736293, -0.18187864027015377, -10.418759484376084, -1.0132938892177468, -0.17326502129079266, -9.925335823946686, -0.9653051453890468, -0.1650593360402707, -9.455280291847409, -0.9195891079871414, -0.1572422651213029, -9.007486193232733, -0.8760381435528001, -0.14979540408696268, -8.580899245391477, -0.8345497160566276, -0.14270122010940484, -8.17451509555231, -0.7950261454890866, -0.13594301070072107},
	'{10.434437110710538, 1.0760923496837065, -0.06891711074802961, 9.881283969676142, 1.1405637001047084, -0.053582495228450495, 9.298391869753319, 1.1954559381298888, -0.038677458501671896, 8.69050254129909, 1.2409155039141384, -0.024266248960443652, 8.06227284872259, 1.277135504798331, -0.010407227158366929, 7.41825235317671, 1.304352381002729, 0.002847184297811084, 6.762862560647742, 1.3228424844230036, 0.01545051466277176, 6.10037789281319, 1.3329185941613548, 0.027362224428507713, 5.434908406443638, 1.334926391653283, 0.03854765193326715, 4.770384275938826, 1.329240917385493, 0.0489779290769246, 4.1105420428552515, 1.3162630302516094, 0.05862986810222621, 3.4589126260418195, 1.296415889569251, 0.06748582147216606, 2.818811076286206, 1.2701414786939313, 0.07553351692961269, 2.1933280502175245, 1.2378971880215195, 0.08276586986661993, 1.5853229696363167, 1.2001524739808105, 0.08918077515808404, 0.9974188244713829, 1.1573856093900825, 0.09478088062807172, 0.43199857021132493, 1.110080539295172, 0.0995733443178109, -0.10879693606121554, 1.0587238551300706, 0.10356957771262819, -0.6230695229845977, 1.0038018987526014, 0.10678497706169178, -1.1091628829706905, 0.945798006615248, 0.1092386448899734},
	'{10.434437110710538, 1.0760923496837065, -0.06891711074802961, 9.881283969676142, 1.1405637001047084, -0.053582495228450495, 9.298391869753319, 1.1954559381298888, -0.038677458501671896, 8.69050254129909, 1.2409155039141384, -0.024266248960443652, 8.06227284872259, 1.277135504798331, -0.010407227158366929, 7.41825235317671, 1.304352381002729, 0.002847184297811084, 6.762862560647742, 1.3228424844230036, 0.01545051466277176, 6.10037789281319, 1.3329185941613546, 0.027362224428507713, 5.434908406443638, 1.334926391653283, 0.03854765193326715, 4.770384275938827, 1.3292409173854929, 0.0489779290769246, 4.110542042855252, 1.3162630302516094, 0.05862986810222621, 3.4589126260418195, 1.2964158895692508, 0.06748582147216606, 2.818811076286206, 1.2701414786939311, 0.07553351692961269, 2.1933280502175245, 1.2378971880215195, 0.08276586986661993, 1.5853229696363171, 1.2001524739808103, 0.08918077515808404, 0.9974188244713833, 1.1573856093900823, 0.09478088062807172, 0.43199857021132493, 1.1100805392951718, 0.0995733443178109, -0.10879693606121554, 1.0587238551300706, 0.10356957771262819, -0.6230695229845977, 1.0038018987526012, 0.10678497706169178, -1.10916288297069, 0.9457980066152478, 0.1092386448899734}};

const real Fbi[0:2][0:59] = '{
	'{-5.002502244065731e-16, 2.2116604277464022e-16, 1.470080668687619e-18, -4.765587957650471e-16, 2.1069180555357794e-16, 1.400458888305981e-18, -4.539893731990653e-16, 2.0071361937175625e-16, 1.3341343367137236e-18, -4.324888194473587e-16, 1.9120799167040084e-16, 1.2709508599367614e-18, -4.120065137845283e-16, 1.821525424785038e-16, 1.2107596993214973e-18, -3.924942328400286e-16, 1.7352595172160557e-16, 1.1534191412986835e-18, -3.7390603706146445e-16, 1.6530790902598836e-16, 1.0987941837341688e-18, -3.561981625548896e-16, 1.5747906590010084e-16, 1.0467562180809946e-18, -3.3932891804745836e-16, 1.500209901806302e-16, 9.971827265844986e-19, -3.232585867298379e-16, 1.4291612263596952e-16, 9.499569938275287e-19, -3.0794933274728263e-16, 1.361477356249088e-16, 9.049678319366345e-19, -2.9336511211921094e-16, 1.296998937132151e-16, 8.621093188022591e-19, -2.79471587877557e-16, 1.2355741615537843e-16, 8.21280548696604e-19, -2.6623604922409725e-16, 1.1770584115319033e-16, 7.823853947020199e-19, -2.5362733451641897e-16, 1.1213139180700636e-16, 7.453322823905894e-19, -2.4161575790120765e-16, 1.0682094367952765e-16, 7.100339742220536e-19, -2.3017303942212033e-16, 1.0176199389573472e-16, 6.764073641524712e-19, -2.1927223843769069e-16, 9.694263170622216e-17, 6.443732819700377e-19, -2.088876901925066e-16, 9.235151044462915e-17, 6.138563068973955e-19, -1.9899494539232267e-16, 8.797782081314213e-17, 5.847845900215814e-19},
	'{3.8792001602566697, -1.323109810553637, -0.19126497126443642, 4.511090742033305, -1.2117710116019829, -0.19100001174534786, 5.087041445125483, -1.0988690495458626, -0.18966075775932295, 5.60645400347202, -0.985121326778791, -0.1873062890410988, 6.06908056756652, -0.8712156958313233, -0.1839986330570126, 6.475008330249903, -0.7578079602042875, -0.17980227081070796, 6.8246429821830965, -0.6455196773023122, -0.17478365235728374, 7.118691147212733, -0.5349362615008024, -0.16901072431808, 7.3581419464531255, -0.4266053837656586, -0.16255247151020177, 7.5442478377376965, -0.3210356627288645, -0.15547847462329312, 7.678504874192352, -0.21869564070851077, -0.14785848569218038, 7.762632522103447, -0.12001303685210263, -0.13976202292897025, 7.798553174046867, -0.02537426837950707, -0.13125798629311797, 7.788371488466303, 0.06487577019164636, -0.12241429499393093, 7.734353681592671, 0.15043368093886184, -0.11329754793794, 7.638906891837724, 0.23103730152002622, -0.10397270795449756, 7.5045587306281245, 0.30646522198837106, -0.09450281045772045, 7.333937127126334, 0.3765360928287819, -0.08494869703230482, 7.129750567465516, 0.44110773815379656, -0.07536877426554539, 6.894768822060503, 0.5000760884388418, -0.06581879798877587},
	'{-3.8792001602566692, 1.3231098105536367, 0.19126497126443642, -4.511090742033305, 1.2117710116019826, 0.19100001174534786, -5.087041445125482, 1.0988690495458624, 0.18966075775932295, -5.60645400347202, 0.9851213267787908, 0.1873062890410988, -6.06908056756652, 0.8712156958313231, 0.1839986330570126, -6.475008330249903, 0.7578079602042873, 0.17980227081070796, -6.824642982183096, 0.6455196773023122, 0.17478365235728374, -7.118691147212733, 0.5349362615008022, 0.16901072431808, -7.3581419464531255, 0.4266053837656584, 0.16255247151020177, -7.5442478377376965, 0.3210356627288644, 0.15547847462329312, -7.678504874192351, 0.21869564070851066, 0.14785848569218038, -7.762632522103447, 0.12001303685210252, 0.13976202292897025, -7.798553174046867, 0.02537426837950696, 0.13125798629311797, -7.788371488466302, -0.06487577019164648, 0.12241429499393093, -7.734353681592671, -0.15043368093886195, 0.11329754793794, -7.638906891837724, -0.23103730152002633, 0.10397270795449756, -7.5045587306281245, -0.3064652219883711, 0.09450281045772045, -7.333937127126334, -0.376536092828782, 0.08494869703230482, -7.129750567465516, -0.4411077381537966, 0.07536877426554539, -6.894768822060503, -0.5000760884388418, 0.06581879798877587}};



