:- table a/2.
%:- import format/2 from format.

a(X,Y) :-
  a(X,Z),  a(Z,Y).
a(X,Y) :- e(X,Y).

go :- 
  cputime(Start),
  a(X,Y),
  cputime(End),
  T is ( End-Start ),
  write('% 200vertices-bprolog.pl: execution time ='), write(T), write(' milliseconds'),nl.

print_solutions :-
  a(X,Y),
  format('BPsol a(~w,~w)~n',[X,Y]),
  fail.

% Test facts
e(0,1).
e(1,2).
e(2,3).
e(3,4).
e(4,5).
e(5,6).
e(6,7).
e(7,8).
e(8,9).
e(9,10).
e(10,11).
e(11,12).
e(12,13).
e(13,14).
e(14,15).
e(15,16).
e(16,17).
e(17,18).
e(18,19).
e(19,20).
e(20,21).
e(21,22).
e(22,23).
e(23,24).
e(24,25).
e(25,26).
e(26,27).
e(27,28).
e(28,29).
e(29,30).
e(30,31).
e(31,32).
e(32,33).
e(33,34).
e(34,35).
e(35,36).
e(36,37).
e(37,38).
e(38,39).
e(39,40).
e(40,41).
e(41,42).
e(42,43).
e(43,44).
e(44,45).
e(45,46).
e(46,47).
e(47,48).
e(48,49).
e(49,50).
e(50,51).
e(51,52).
e(52,53).
e(53,54).
e(54,55).
e(55,56).
e(56,57).
e(57,58).
e(58,59).
e(59,60).
e(60,61).
e(61,62).
e(62,63).
e(63,64).
e(64,65).
e(65,66).
e(66,67).
e(67,68).
e(68,69).
e(69,70).
e(70,71).
e(71,72).
e(72,73).
e(73,74).
e(74,75).
e(75,76).
e(76,77).
e(77,78).
e(78,79).
e(79,80).
e(80,81).
e(81,82).
e(82,83).
e(83,84).
e(84,85).
e(85,86).
e(86,87).
e(87,88).
e(88,89).
e(89,90).
e(90,91).
e(91,92).
e(92,93).
e(93,94).
e(94,95).
e(95,96).
e(96,97).
e(97,98).
e(98,99).
e(99,100).
e(100,101).
e(101,102).
e(102,103).
e(103,104).
e(104,105).
e(105,106).
e(106,107).
e(107,108).
e(108,109).
e(109,110).
e(110,111).
e(111,112).
e(112,113).
e(113,114).
e(114,115).
e(115,116).
e(116,117).
e(117,118).
e(118,119).
e(119,120).
e(120,121).
e(121,122).
e(122,123).
e(123,124).
e(124,125).
e(125,126).
e(126,127).
e(127,128).
e(128,129).
e(129,130).
e(130,131).
e(131,132).
e(132,133).
e(133,134).
e(134,135).
e(135,136).
e(136,137).
e(137,138).
e(138,139).
e(139,140).
e(140,141).
e(141,142).
e(142,143).
e(143,144).
e(144,145).
e(145,146).
e(146,147).
e(147,148).
e(148,149).
e(149,150).
e(150,151).
e(151,152).
e(152,153).
e(153,154).
e(154,155).
e(155,156).
e(156,157).
e(157,158).
e(158,159).
e(159,160).
e(160,161).
e(161,162).
e(162,163).
e(163,164).
e(164,165).
e(165,166).
e(166,167).
e(167,168).
e(168,169).
e(169,170).
e(170,171).
e(171,172).
e(172,173).
e(173,174).
e(174,175).
e(175,176).
e(176,177).
e(177,178).
e(178,179).
e(179,180).
e(180,181).
e(181,182).
e(182,183).
e(183,184).
e(184,185).
e(185,186).
e(186,187).
e(187,188).
e(188,189).
e(189,190).
e(190,191).
e(191,192).
e(192,193).
e(193,194).
e(194,195).
e(195,196).
e(196,197).
e(197,198).
e(198,199).
