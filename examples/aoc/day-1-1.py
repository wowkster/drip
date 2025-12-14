
dial = 50
zero_count = 0

file = open("examples/aoc/day-1-1.txt", "r")
for line in file.readlines():
    sign = 1
    
    if line[0] == 'L':
        sign = -1
        
    parsed = 0
    
    for c in line[1:-1]:
         parsed = parsed * 10 + int(c)
         
    rotation = parsed * sign
    
    dial = (dial + rotation) % 100
    
    if dial == 0:
        zero_count += 1
        
print('dial =', dial)
print('zero_count =', zero_count)