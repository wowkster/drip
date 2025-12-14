
dial = 50
zero_count = 0

file = open("examples/aoc/day-1.txt", "r")
for line in file.readlines():
    sign = 1
    
    if line[0] == 'L':
        sign = -1
        
    parsed = 0
    
    for c in line[1:-1]:
         parsed = parsed * 10 + int(c)
         
    rotation = parsed * sign
    
    new_dial = dial + rotation
    
    print('=================')
    print('rotation =', rotation)
    print('previous =', dial)
    print('new_dial =', new_dial)
    print('new_dial % 100 =', new_dial % 100)

    added = 0
    
    if new_dial < 0:
        added += abs(new_dial // 100) # passed at least once
        if dial == 0:
            added -= 1
    elif new_dial > 0:
        added += (new_dial - 1) // 100 # 
        
    dial = new_dial % 100

    if dial == 0:
        added += 1
        
    print('added = ', added)
        
    zero_count += added
        
print('==========END==========')
print('dial =', dial)
print('zero_count =', zero_count)
